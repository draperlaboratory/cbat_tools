(***************************************************************************)
(*                                                                         *)
(*  Copyright (C) 2018 The Charles Stark Draper Laboratory, Inc.           *)
(*                                                                         *)
(*  This file is provided under the license found in the LICENSE file in   *)
(*  the top-level directory of this project.                               *)
(*                                                                         *)
(*  This work is funded in part by ONR/NAWC Contract N6833518C0107.  Its   *)
(*  content does not necessarily reflect the position or policy of the US  *)
(*  Government and no official endorsement should be inferred.             *)
(*                                                                         *)
(***************************************************************************)


(* This plugin is intended to utilize the results of value-set analysis to
   complete a program's CFG by replacing indirect jumps with direct ones
   where possible. It does this by replacing each indirect jump with a
   sequence of conditional direct jumps when the possible targets can be
   reduced to a sufficiently small number. *)
     
open !Core_kernel.Std
open Bap.Std
open Graphlib.Std
include Self()

module AI = Cbat_ai_representation
module Utils = Cbat_vsa_utils
module Clp = Cbat_clp_set_composite
module Vsa = Cbat_vsa

type create_t = ?tid:tid -> ?cond:exp -> label -> jmp term

(* cond' = cond && (e = w) *)
let specialize_cond cond e w : exp =
  Bil.BinOp (Bil.AND, cond, Bil.BinOp (Bil.EQ, e, Bil.Int w))

let create_label terms w : label =
  let has_address w b = Option.value_map ~default:false
      (Term.get_attr b address) ~f:(fun addr -> addr = w) in
  match Seq.find terms ~f:(has_address w) with
  | Some b -> (Direct (Term.tid b))
  | None -> (Indirect (Bil.Int w))

let create_blk_label s w : label =
  (* TODO: what if the location to be jumped to wasn't identified as a block before? *)
  let blks = Term.enum blk_t s in
  create_label blks w

let create_call_label prog w : label =
  (* TODO: what if the location to be jumped to wasn't identified as a sub before? *)
  let subs = Term.enum sub_t prog in
  create_label subs w

let concrete_jump (create : create_t) s cond e w : jmp term =
  let cond = specialize_cond cond e w in
  let lbl = create_blk_label s w in
  match lbl with
  | Direct _ -> Jmp.create_goto ~cond lbl
  | Indirect _ -> create ~cond lbl

type is_done = Done | EdgesAdded

let both_done d1 d2 : is_done = match d1, d2 with
  | EdgesAdded, _ -> EdgesAdded
  | _, EdgesAdded -> EdgesAdded
  | Done, Done -> Done

(* TODO: add_edges contains duplicated code/should be simplifiable *)
let add_edges (prog : program term) (s : sub term) (postcondition : AI.t) (b : blk term) : blk term * is_done =
  let jump_builder = Blk.Builder.init ~copy_phis:true ~copy_defs:true b in
  let conds = ref [] in
  let edges_added = ref Done in
  edges_added := Done;
  Term.enum jmp_t b
  (* TODO: this is not sound to do before the CFG is complete.
     Make a separate plugin or do at the end?
     |> Vsa.reachable_jumps postcondition
  *)
  (* keep all direct jumps and attempt to enumerate the cases of indirect jumps *)
  |> Seq.iter  ~f:begin fun j -> begin match Jmp.kind j with
    | Goto (Direct _) | Ret (Direct _) -> ()
    | Goto (Indirect e) | Ret (Indirect e) ->
      let targets = Utils.exn_on_err @@ Vsa.denote_imm_exp e postcondition in
      let cardn = Clp.cardinality targets in
      if cardn > Word.of_int !Utils.max_edge_explosion ~width:(Word.bitwidth cardn)
      then Printf.printf "//Edge transform produced edge explosion@."
      else List.iter (Clp.iter targets) ~f:begin fun w ->
          (* TODO: this cond is computed twice; fix *)
          let cond = specialize_cond (Jmp.cond j) e w in
          let new_j = concrete_jump Jmp.create_goto s (Jmp.cond j) e w in
          if not @@ List.mem !conds cond ~equal:Bap.Std.Exp.equal
          (* TODO: this fix should not be necessary; investigate further *)
          && not (Bap.Std.Exp.equal e (Bil.Int w)) then begin
            Blk.Builder.add_jmp jump_builder new_j;
            edges_added := EdgesAdded;
            conds := cond::!conds;
          end
        end
    | Call c ->
      (* TODO: specialize return when possible. (Low priority; rarely needed) *)
      begin match Call.target c with
        | Direct _ -> ()
        | Indirect e ->
          let targets = Utils.exn_on_err @@ Vsa.denote_imm_exp e postcondition in
          let cardn = Clp.cardinality targets in
          if cardn > Word.of_int !Utils.max_edge_explosion ~width:(Word.bitwidth cardn)
          then Printf.printf "//Edge transform produced edge explosion@."
          else List.iter (Clp.iter targets) ~f:begin fun w ->
              let cond = specialize_cond (Jmp.cond j) e w in
              let lbl = create_call_label prog w in
              let new_c = Call.with_target c lbl in
              let new_j = Jmp.create_call ~cond new_c in
              if not @@ List.mem !conds cond ~equal:Bap.Std.Exp.equal then begin
                Blk.Builder.add_jmp jump_builder new_j;
                edges_added := EdgesAdded;
                conds := cond::!conds;
              end
            end
      end
    | Int _ -> Utils.not_implemented ~top:() "Edge concretization for interrupt";
    end;
    (* We always add the original jump back *)
    Blk.Builder.add_jmp jump_builder j;
    conds := (Jmp.cond j)::!conds;
  end;
  let blk = Blk.Builder.result jump_builder in
  let blk = Term.with_attrs blk (Term.attrs b) in
  blk, !edges_added

let insert_edges prog sub sol : sub term * is_done =
  Term.enum blk_t sub
  |> Seq.fold ~init:(sub, Done) ~f:begin fun (sub, edges_added) blk ->
    let bid = Term.tid blk in
    let vsa_res = Solution.get sol bid in
    let vsa_res_post = Vsa.denote_defs blk vsa_res in
    let res, changed = add_edges prog sub vsa_res_post blk in
    let edges_added = both_done edges_added changed in
    let sub' = Term.update blk_t sub res in
    sub', edges_added
end

let rec do_until_done ?fuel (f : 'a -> 'a * is_done) (arg : 'a) : 'a =
  if fuel = Some 0 then begin
    Printf.printf "@.Giving up on edge addition; could not find fixpoint!@.";
    arg
  end else
    let res1, done_ = f arg in
    match done_ with
    | Done -> res1
    | EdgesAdded -> do_until_done ?fuel:(Option.map fuel ~f:pred) f res1

let recompute_vsa prog sub : sub term =
  let sol = Vsa.static_graph_vsa [] prog sub (Vsa.init_sol sub) in
  (* TODO: this can be affected by the effects on unreachable blocks;
     is there a way to skip some of that?
  *)
  Term.map blk_t sub ~f:begin fun blk ->
    Term.tid blk
    |> Solution.get sol
    |> Term.set_attr blk Vsa.precond
  end

let main (sub_name : string option) (proj : project) : project =
  let perform_step (proj : project) : project * is_done =
    let prog = Project.program proj in
    Term.enum sub_t prog
    |> Seq.fold ~init:(prog, Done) ~f:begin fun (prog, done_) sub ->
      let open Monads.Std.Monad.Option.Syntax in
      let sname = Sub.name sub in
      if Option.value ~default:sname sub_name = sname then
        let sol = Option.value_exn ~message:"VSA not stored!" (Vsa.load sub) in
        let sub', edges_added = insert_edges prog sub sol in
        let prog' = Term.update sub_t prog sub' in
        match edges_added with
        | EdgesAdded ->
          let sub_vsa = recompute_vsa prog' sub' in
          let prog_vsa = Term.update sub_t prog' sub_vsa in
          prog_vsa, EdgesAdded
        | Done -> prog', done_
      else prog, done_
    end
    |> (fun (prog,d) -> Project.with_program proj prog, d)
  in do_until_done perform_step proj

module Cmdline = struct
  open Config
  let sub = param (some string) "sub" ~doc:"Name of subroutine to transform"

  let () = when_ready (fun {get=(!!)} ->
      (* We depend on value-set so that its settings affect this plugin *)
      Project.register_pass ~deps:["value-set"] (main !!sub))

  let () = manpage [
      `S "DESCRIPTION";
      `P
        ("Makes edges in the control-flow graph explicit by rewriting jumps"^
      " to be direct (target specific locations/tids) where possible.")
    ]
end
