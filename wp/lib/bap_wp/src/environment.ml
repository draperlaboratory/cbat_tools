(***************************************************************************)
(*                                                                         *)
(*  Copyright (C) 2018/2019 The Charles Stark Draper Laboratory, Inc.      *)
(*                                                                         *)
(*  This file is provided under the license found in the LICENSE file in   *)
(*  the top-level directory of this project.                               *)
(*                                                                         *)
(*  This work is funded in part by ONR/NAWC Contract N6833518C0107.  Its   *)
(*  content does not necessarily reflect the position or policy of the US  *)
(*  Government and no official endorsement should be inferred.             *)
(*                                                                         *)
(***************************************************************************)

open !Core_kernel
open Bap.Std
open Graphlib.Std

include Self()

module Expr = Z3.Expr
module Constr = Constraint

(* The environment for computing the semantics of an instruction *)
module EnvMap = Var.Map
module TidMap = Tid.Map
module StringMap = String.Map

type var_gen = int ref

type t = {
  freshen : bool;
  ctx : Z3.context;
  var_gen : var_gen;
  subs : Sub.t Seq.t;
  var_map : Constr.z3_expr EnvMap.t;
  precond_map : Constr.t TidMap.t;
  fun_name_tid : Tid.t StringMap.t;
  call_map : string TidMap.t;
  sub_handler : fun_spec TidMap.t;
  jmp_handler : jmp_spec;
  int_handler : int_spec;
  loop_handler : loop_handler;
  exp_conds : exp_cond list;
  arch : Arch.t;
  fun_input_regs : bool
}

and fun_spec_type =
  | Summary of (t -> Constr.t -> Tid.t -> Constr.t * t)
  | Inline

and fun_spec = {
  spec_name : string;
  spec : fun_spec_type
}

and jmp_spec = t -> Constr.t -> Tid.t -> Jmp.t -> (Constr.t * t) option

and int_spec = t -> Constr.t -> int -> Constr.t * t

and loop_handler = {
  (* Updates the environment with the preconditions computed by
     the loop handling procedure for the appropriate blocks *)
  handle : t -> Constr.t -> start:Graphs.Ir.Node.t -> Graphs.Ir.t -> t
}

and cond_type = Verify of Constr.goal | Assume of Constr.goal

and exp_cond = t -> Bap.Std.Exp.t -> cond_type option

let mk_ctx () : Z3.context = Z3.mk_context []

let mk_var_gen () : int ref = ref 0

let mk_z3_expr (ctx : Z3.context) ~name:(name : string) ~typ:(typ : Type.t) : Constr.z3_expr =
  match typ with
  | Type.Imm size -> Z3.BitVector.mk_const_s ctx name size
  | Type.Mem (i_size, w_size) ->
    debug "Creating memory Mem<%d,%d>%!" (Size.in_bits i_size) (Size.in_bits w_size);
    let i_sort = Z3.BitVector.mk_sort ctx (Size.in_bits i_size) in
    let w_sort = Z3.BitVector.mk_sort ctx (Size.in_bits w_size) in
    Z3.Z3Array.mk_const_s ctx name i_sort w_sort
  | Type.Unk ->
    error "Unk type: Unable to make z3_expr %s.%!" name;
    failwith "mk_z3_expr: type is not representable by Type.t"

let add_precond (env : t) (tid : Tid.t) (p : Constr.t) : t =
  { env with precond_map = TidMap.set env.precond_map ~key:tid ~data:p }

let get_precondition (env : t) (tid : Tid.t) : Constr.t option =
  if not (TidMap.mem env.precond_map tid) then
    warning "Precondition for block %s not found!%!" (Tid.to_string tid);
  TidMap.find env.precond_map tid

let get_context (env : t) : Z3.context =
  env.ctx

let init_fun_name (subs : Sub.t Seq.t) : Tid.t StringMap.t =
  Seq.fold subs ~init:StringMap.empty
    ~f:(fun map sub ->
        StringMap.set map ~key:(Sub.name sub) ~data:(Term.tid sub))

let get_fresh ?name:(n = "fresh_") (var_seed : var_gen) : string =
  incr var_seed;
  n ^ (string_of_int !var_seed)

let new_z3_expr ?name:(name = "fresh_") (env: t) (typ : Type.t) : Constr.z3_expr =
  let ctx = env.ctx in
  let var_seed = env.var_gen in
  mk_z3_expr ctx ~name:(get_fresh ~name:name var_seed) ~typ:typ

let init_call_map (var_gen : var_gen) (subs : Sub.t Seq.t) : string TidMap.t =
  Seq.fold subs ~init:TidMap.empty
    ~f:(fun map sub ->
        let is_called = get_fresh ~name:("called_" ^ (Sub.name sub)) var_gen in
        TidMap.set map ~key:(Term.tid sub) ~data:is_called)

let init_sub_handler (subs : Sub.t Seq.t) (arch : Arch.t)
    ~specs:(specs : (Sub.t -> Arch.t -> fun_spec option) list)
    ~default_spec:(default_spec : Sub.t -> Arch.t -> fun_spec) : fun_spec TidMap.t =
  Seq.fold subs ~init:TidMap.empty
    ~f:(fun map sub ->
        let spec = List.find_map specs ~f:(fun creator -> creator sub arch)
                   |> Option.value ~default:(default_spec sub arch) in
        debug "%s: %s%!" (Sub.name sub) spec.spec_name;
        TidMap.set map ~key:(Term.tid sub) ~data:spec)

(* FIXME: this is something of a hack: we use a function ref as a
   place holder for the WP transform for subroutines, which itself is
   needed in the loop handler defined in the environment.

   It will be substituted by the actual visit_sub function at the
   point of definition. This is used to simulate "open recursion".  *)
let wp_rec_call :
  (t -> Constr.t -> start:Graphs.Ir.Node.t -> Graphs.Ir.t -> t) ref =
  ref (fun _ _ ~start:_ _ -> assert false)

let trivial_pre (env : t) : Constr.t =
  let ctx = get_context env in
  Z3.Boolean.mk_true ctx
  |> Constr.mk_goal "true"
  |> Constr.mk_constr

(* Looks up the precondition of the exit node of a loop by:
   - obtaining the post dominator tree
   - for each node in the SCC, find its parent in the dominator tree
   - if the parent node is not in the original SCC, it is an exit node *)
let loop_exit_pre (env : t) (node : Graphs.Ir.Node.t) (graph : Graphs.Ir.t)
  : Constr.t option =
  let module Node = Graphs.Ir.Node in
  let scc = Graphlib.strong_components (module Graphs.Ir) graph in
  match Partition.group scc node with
  | None -> None
  | Some g ->
    let leaf = Seq.find (Graphlib.postorder_traverse (module Graphs.Ir) graph)
        ~f:(fun n -> Seq.is_empty (Node.succs n graph))
    in
    match leaf with
    | None -> None
    | Some l ->
      let dom_tree = Graphlib.dominators (module Graphs.Ir) ~rev:true graph l in
      let exit_node = Seq.find_map (Group.enum g) ~f:(fun n ->
          match Tree.parent dom_tree n with
          | None -> None
          | Some p ->
            if Group.mem g p then
              None
            else
              Some (p |> Node.label |> Term.tid)
        ) in
      match exit_node with
      | None -> None
      | Some e ->
        debug "Using precondition from node %s%!" (Tid.to_string e);
        get_precondition env e

let init_loop_unfold (num_unroll : int) : loop_handler =
  {
    handle =
      let module Node = Graphs.Ir.Node in
      let depth : (Blk.t, int) Hashtbl.t = Hashtbl.create (module Blk) in
      let find_depth node = Hashtbl.find_or_add depth (Node.label node)
          ~default:(fun () -> num_unroll)
      in
      let decr_depth node =
        Hashtbl.update depth (Node.label node) ~f:(function None -> assert false | Some n -> n-1)
      in
      let unroll env pre ~start:node g =
        if find_depth node <= 0 then
          let tid = node |> Node.label |> Term.tid in
          let pre =
            match List.find_map [loop_exit_pre] ~f:(fun spec -> spec env node g) with
            | Some p -> p
            | None ->
              warning "Trivial precondition is being used for node %s%!" (Tid.to_string tid);
              trivial_pre env
          in
          add_precond env tid pre
        else
          begin
            decr_depth node;
            !wp_rec_call env pre ~start:node g
          end
      in
      unroll
  }

let mk_env
    ~subs:(subs : Sub.t Seq.t)
    ~specs:(specs : (Sub.t -> Arch.t -> fun_spec option) list)
    ~default_spec:(default_spec : Sub.t -> Arch.t -> fun_spec)
    ~jmp_spec:(jmp_spec : jmp_spec)
    ~int_spec:(int_spec : int_spec)
    ~exp_conds:(exp_conds : exp_cond list)
    ~num_loop_unroll:(num_loop_unroll : int)
    ~arch:(arch : Arch.t)
    ~freshen_vars:(freshen_vars : bool)
    ~fun_input_regs:(fun_input_regs : bool)
    (ctx : Z3.context)
    (var_gen : var_gen)
  : t =
  {
    freshen = freshen_vars;
    ctx = ctx;
    var_gen = var_gen;
    subs = subs;
    var_map = EnvMap.empty;
    precond_map = TidMap.empty;
    fun_name_tid = init_fun_name subs;
    call_map = init_call_map var_gen subs;
    sub_handler = init_sub_handler subs arch ~specs:specs ~default_spec:default_spec;
    jmp_handler = jmp_spec;
    int_handler = int_spec;
    loop_handler = init_loop_unfold num_loop_unroll;
    exp_conds = exp_conds;
    arch = arch;
    fun_input_regs = fun_input_regs
  }

let env_to_string (env : t) : string =
  let pair_printer ts1 ts2 f (x,y) = Format.fprintf f "%s -> \n%s\n" (ts1 x) (ts2 y) in
  let map_seq_printer ts1 ts2 f seq = Seq.pp (pair_printer ts1 ts2) f seq in
  let var_list = env.var_map |> EnvMap.to_sequence in
  let sub_list = env.sub_handler |> TidMap.to_sequence in
  let call_list = env.call_map |> TidMap.to_sequence in
  let precond_list = env.precond_map |> TidMap.to_sequence in
  Format.asprintf "Vars: %a\nSubs: %a\nCalls: %a\nPreconds: %a%!"
    (map_seq_printer Var.to_string Expr.to_string) var_list
    (map_seq_printer Tid.to_string (fun s -> s.spec_name)) sub_list
    (map_seq_printer Tid.to_string ident) call_list
    (map_seq_printer Tid.to_string Constr.to_string) precond_list

let set_freshen (env : t) (freshen : bool) = { env with freshen = freshen }

let add_var (env : t) (v : Var.t) (x : Constr.z3_expr) : t =
  { env with var_map = EnvMap.set env.var_map ~key:v ~data:x }

let remove_var (env :t) (v : Var.t) : t =
  { env with var_map = EnvMap.remove env.var_map v }

let mk_exp_conds (env : t) (e : exp) : Constr.goal list * Constr.goal list =
  let { exp_conds; _ } = env in
  let conds = List.map exp_conds ~f:(fun gen -> gen env e) in
  let conds = List.filter_opt conds in
  List.partition_map conds
    ~f:(function | Assume cond -> `Fst cond | Verify cond -> `Snd cond)

let get_var_gen (env : t) : var_gen =
  env.var_gen

let get_subs (env : t) : Sub.t Seq.t =
  env.subs

let get_var_map (env : t) : Constr.z3_expr EnvMap.t =
  env.var_map

let find_var (env : t) (var : Var.t) : Constr.z3_expr option =
  EnvMap.find env.var_map var

let get_var (env : t) (var : Var.t) : Constr.z3_expr * t =
  let mv = EnvMap.find env.var_map var in
  match mv with
  | Some v -> v, env
  | None ->
    let typ = Var.typ var in
    let full_name = Var.name var ^ (string_of_int (Var.index var)) in
    if env.freshen then
      let v = new_z3_expr ~name:full_name env typ in
      v, add_var env var v
    else
      let ctx = env.ctx in
      let v = mk_z3_expr ctx ~name:full_name ~typ:typ in
      v, add_var env var v

let get_sub_name (env : t) (tid : Tid.t) : string option =
  Seq.find_map env.subs ~f:(fun s ->
      if Tid.equal tid (Term.tid s) then
        Some (Sub.name s)
      else
        None)

let get_fun_name_tid (env : t) (f : string) : Tid.t option =
  StringMap.find env.fun_name_tid f

let get_called (env : t) (tid : Tid.t) : string option =
  TidMap.find env.call_map tid

let get_sub_handler (env : t) (tid : Tid.t) : fun_spec_type option =
  match TidMap.find env.sub_handler tid with
  | Some compute_func -> Some compute_func.spec
  | None -> None

let get_jmp_handler (env : t) : jmp_spec =
  env.jmp_handler

let get_int_handler (env : t) : int_spec =
  env.int_handler

let get_loop_handler (env : t) :
  t -> Constr.t -> start:Graphs.Ir.Node.t -> Graphs.Ir.t -> t =
  env.loop_handler.handle

let get_arch (env : t) : Arch.t =
  env.arch

let fold_fun_tids (env : t) ~init:(init : 'a)
    ~f:(f : key:string -> data:Tid.t -> 'a -> 'a) : 'a =
  StringMap.fold env.fun_name_tid ~init:init ~f:f

let is_x86 (a : Arch.t) : bool =
  match a with
  | #Arch.x86 -> true
  | _ -> false

let use_input_regs (env : t) : bool =
  env.fun_input_regs
