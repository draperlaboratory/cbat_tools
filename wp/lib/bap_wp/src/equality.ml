open !Core_kernel
open Bap.Std
open Graphlib.Std
open Base__Option.Monad_infix

module Ir = Bap.Std.Graphs.Ir
module OcamlGraph = Graphlib.To_ocamlgraph (Ir)
module BFS = Graph.Traverse.Bfs (OcamlGraph)

(* Replaces the real variables with indices with only their base *)
let strip_indices (e : Exp.t) : Exp.t =
  let visitor =
    (object
      inherit Exp.mapper as super
      method! map_let var ~exp:exp1 ~body:exp2 =
        Let (Var.base var, super#map_exp exp1, super#map_exp exp2)
      method! map_var v = Var (Var.base v)
    end) in
  visitor#map_exp e

(* Perform variable lookup in map. BOTH variables must be virtual.
   If they are not, then fail and return None.*)
let map_var (vmap : Var.t Var.Map.t)
    (v1 : Var.t) (v2 : Var.t) : (Var.t Var.Map.t * Var.t) option  =
  match Var.Map.find vmap v1 with
  (* if not found in map, add to map *)
  | None ->
    (* if is virtual, do mapping *)
    if Var.is_virtual v1 && Var.is_virtual v2 then
      Some (Var.Map.add_exn vmap ~key:v1 ~data:v2, v2)
      (* if is physical register, just return original variable *)
    else Some (vmap, v1)
  (* if found in map, return what is found *)
  | Some v_found -> Some (vmap, v_found)

(* Maps all virtual variables from e1 to their analagous variable within vmap;
   if a variable not in vmap, is added to vmap from e2.
   Returns None if cannot map variables because subs do not match in structure *)
let rec sub_exp (vmap : Var.t Var.Map.t)
    (e1 : Exp.t) (e2 : Exp.t) : (Var.t Var.Map.t * Exp.t) option =
  let open Bap.Std.Bil.Types in
  match e1, e2 with
  | Load (exp1_bin1, exp2_bin1, endian, size),
    Load (exp1_bin2, exp2_bin2, _, _) ->
    sub_exp vmap exp1_bin1 exp1_bin2 >>=
    fun (vmap, exp1_bin1) -> sub_exp vmap exp2_bin1 exp2_bin2 >>|
    fun (vmap, exp2_bin1) -> vmap, Load (exp1_bin1, exp2_bin1, endian, size)
  | Store (exp1_bin1, exp2_bin1, exp3_bin1, endian, size),
    Store (exp1_bin2, exp2_bin2, exp3_bin2, _, _) ->
    sub_exp vmap exp1_bin1 exp1_bin2 >>=
    fun (vmap, exp1_bin1) -> sub_exp vmap exp2_bin1 exp2_bin2 >>=
    fun (vmap, exp2_bin1) -> sub_exp vmap exp3_bin1 exp3_bin2 >>|
    fun (vmap, exp3_bin1) -> vmap, Store (exp1_bin1, exp2_bin1, exp3_bin1, endian, size)
  | BinOp (binop, exp1_bin1, exp2_bin1), BinOp (_, exp1_bin2, exp2_bin2) ->
    sub_exp vmap exp1_bin1 exp1_bin2 >>=
    fun (vmap, exp1_bin1) -> sub_exp vmap exp2_bin1 exp2_bin2 >>|
    fun (vmap, exp2_bin1) -> vmap, BinOp (binop, exp1_bin1, exp2_bin1)
  | UnOp (unop, exp1_bin1), UnOp (_, exp1_bin2) ->
    sub_exp vmap exp1_bin1 exp1_bin2 >>|
    fun (vmap, exp1_bin1) -> vmap, UnOp (unop, exp1_bin1)
  | Var v_bin1, Var v_bin2 -> map_var vmap v_bin1 v_bin2 >>|
    fun (vmap, v_bin1) -> vmap, Var v_bin1
  | Bap.Std.Bil.Types.Int w, Bap.Std.Bil.Types.Int _ ->
    Some (vmap, Bap.Std.Bil.Types.Int w)
  | Cast (cast, i, exp1_bin1), Cast (_, _, exp1_bin2) ->
    sub_exp vmap exp1_bin1 exp1_bin2 >>|
    fun (vmap, exp1_bin1) ->
    vmap, Cast (cast, i, exp1_bin1)
  | Let (var_bin1, exp1_bin1, exp2_bin1), Let (var_bin2, exp1_bin2, exp2_bin2) ->
    sub_exp vmap exp1_bin1 exp1_bin2 >>=
    fun (vmap, exp1_bin1) ->
    sub_exp vmap exp2_bin1 exp2_bin2 >>=
    fun (vmap, exp2_bin1) -> map_var vmap var_bin1 var_bin2 >>|
    fun (vmap, var_bin1) ->
    vmap, Let (var_bin1, exp1_bin1, exp2_bin1)
  | Unknown (s, typ), Unknown _ -> Some (vmap, Unknown (s, typ))
  | Ite (exp1_bin1, exp2_bin1, exp3_bin1),
    Ite (exp1_bin2, exp2_bin2, exp3_bin2) ->
    sub_exp vmap exp1_bin1 exp1_bin2 >>=
    fun (vmap, exp1_bin1) -> sub_exp vmap exp2_bin1 exp2_bin2 >>=
    fun (vmap, exp2_bin1) -> sub_exp vmap exp3_bin1 exp3_bin2 >>|
    fun (vmap, exp3_bin1) -> vmap, Ite (exp1_bin1, exp2_bin1, exp3_bin1)
  | Extract (i, j, exp_bin1), Extract (_, _, exp_bin2) ->
    sub_exp vmap exp_bin1 exp_bin2 >>|
    fun (vmap, exp_bin1) -> vmap, Extract (i, j, exp_bin1)
  | Concat (exp1_bin1, exp2_bin1), Concat (exp1_bin2, exp2_bin2) ->
    sub_exp vmap exp1_bin1 exp1_bin2 >>=
    fun (vmap, exp1_bin1) -> sub_exp vmap exp2_bin1 exp2_bin2 >>|
    fun (vmap, exp2_bin1) -> vmap, Concat (exp1_bin1, exp2_bin1)
  | _, _ -> None

(* Compares two defs; returns the updated varmap if they match; returns None
 * if do not match. Only compares expressions and structure. *)
let compare_def (def1 : def term) (def2 : def term) (vmap_orig : Var.t Var.Map.t)
  : (Var.t Var.Map.t) option  =
  let var1_orig, var2 =
    Bap.Std.Bil.Types.Var (Def.lhs def1), Bap.Std.Bil.Types.Var (Def.lhs def2) in
  let var1_orig, var2 = strip_indices var1_orig, strip_indices var2 in
  sub_exp vmap_orig var1_orig var2 >>= fun (vmap, var1) ->
  let lhs_is_equal = Exp.equal var1 var2 in
  let rhs1_orig, rhs2 = Def.rhs def1, Def.rhs def2 in
  let rhs1_orig, rhs2 = strip_indices rhs1_orig, strip_indices rhs2 in
  sub_exp vmap rhs1_orig rhs2 >>= fun (vmap, rhs1) ->
  let rhs_is_equal = Exp.equal rhs1 rhs2 in
  if rhs_is_equal && lhs_is_equal then
    Some vmap
  else None

(* Compares label based on only expression and structure. *)
let compare_lbl (lbl1 : label) (lbl2 : label) (map : Var.t Var.Map.t) : (Var.t Var.Map.t) option =
  match lbl1, lbl2 with
  | Direct _tid1, Direct _tid2 -> (* to be checked later on *) Some map
  | Indirect exp1, Indirect exp2 ->
    let exp1, exp2 = strip_indices exp1, strip_indices exp2 in
    sub_exp map exp1 exp2 >>=
    fun (map, exp1) ->
    if Exp.equal exp1 exp2 then
      Some map
    else None
  | _, _ -> None

(* Compares two things:
   - jmp1 and jmp2 match in structure
   - jmp1 and jmp2 match in all Exp.ts contained within *)
let compare_jmp (jmp1 : jmp term) (jmp2 : jmp term) (map : Var.t Var.Map.t) :
  (Var.t Var.Map.t) option =
  match Jmp.kind jmp1, Jmp.kind jmp2 with
  | Goto label1, Goto label2 -> compare_lbl label1 label2 map
  | Call call1, Call call2 ->
    begin
      let target1, target2 = Call.target call1, Call.target call2 in
      compare_lbl target1 target2 map >>=
      fun map ->
      match Call.return call1, Call.return call2 with
      | Some label1, Some label2 -> compare_lbl label1 label2 map
      | None, None -> Some map
      | _, _ -> None
    end
  | Ret label1, Ret label2 -> compare_lbl label1 label2 map
  | Int (code1, _tid1), Int (code2, _tid2) -> if code1 = code2 then Some map else None
  | _, _ -> None

(* There should be no phi terms. Fail if there are. *)
let compare_phis (phis1 : (phi term) list) (phis2 : (phi term) list)
    (map : Var.t Var.Map.t) : (Var.t Var.Map.t) option =
  if List.length phis1 > 0 || List.length phis2 > 0 then None
  else Some map

(* Check that all defs in two lists match in expression and structure but not TID. *)
let compare_defs (defs1 : (def term) list)
    (defs2 : (def term) list) (map : Var.t Var.Map.t) : (Var.t Var.Map.t) option =
  match List.zip defs1 defs2 with
  | Core_kernel.List.Or_unequal_lengths.Unequal_lengths -> None
  | Core_kernel.List.Or_unequal_lengths.Ok z ->
    List.fold z ~init:(Some map)
      ~f:(fun (map_wrap) (d1, d2) ->
          match map_wrap with
          | None -> None
          | Some map -> compare_def d1 d2 map)

(* Check that all jmps in a list match in expression and structure but not TID. *)
let compare_jmps (jmps1 : (jmp term) list) (jmps2 : (jmp term) list)
    (map : Var.t Var.Map.t) : (Var.t Var.Map.t) option =
  match List.zip jmps1 jmps2 with
  | Core_kernel.List.Or_unequal_lengths.Unequal_lengths -> None
  | Core_kernel.List.Or_unequal_lengths.Ok z ->
    List.fold z ~init:(Some map)
      ~f:(fun (map_wrap) (j1, j2) ->
          match map_wrap with
          | Some map -> compare_jmp j1 j2 map
          | None -> None)

(* Compares everything about a block EXCEPT tids, which will be done later. *)
let compare_block (blk1 : blk term) (blk2 : blk term) map =
  compare_defs (Term.enum def_t blk1 |> Sequence.to_list)
    (Term.enum def_t blk2 |> Sequence.to_list) map >>=
  fun map -> compare_jmps (Term.enum jmp_t blk1 |> Sequence.to_list)
    (Term.enum jmp_t blk2 |> Sequence.to_list) map >>=
  fun map -> compare_phis (Term.enum phi_t blk1 |> Sequence.to_list)
    (Term.enum phi_t blk2 |> Sequence.to_list) map

(* Iterate through all reachable nodes in each cfg
 *  and generate a map from node tid to that node's blk.*)
let get_node_map (cfg1 : Ir.t) : (blk term) Tid.Map.t =
  let acc = fun ele tid_map ->
    let tid = Term.tid (Ir.Node.label ele) in
    Tid.Map.update tid_map tid ~f:(fun _ -> Ir.Node.label ele) in
  BFS.fold acc Tid.Map.empty cfg1

let compare_blocks_syntax (sub1: Sub.t) (sub2 : Sub.t) :
  (Tid.Set.t Tid.Map.t) * (((Var.t Var.Map.t) Tid.Map.t) Tid.Map.t) =
  let cfg1, cfg2 = Sub.to_cfg sub1, Sub.to_cfg sub2 in
  (* blk1 tid -> set{blk2 tids} *)
  let blk_map = Tid.Map.empty in
  (* blk1 tid, blk2 tid -> varmap *)
  let blk_varmap = Tid.Map.empty in
  let evaluator = (fun (node1 : Ir.Node.t) (blk_map, blk_varmap) ->
      let blk1 = Ir.Node.label node1 in
      let tid1 = Term.tid blk1 in
      let inner_evaluator =
        (fun (node2 : Ir.Node.t) (blk_map, blk_varmap) ->
           let blk2 = Ir.Node.label node2 in
           let tid2 = Term.tid blk2 in
           let v_map = Var.Map.empty in
           match compare_block blk1 blk2 v_map with
           | Some v_map ->
             (Tid.Map.update blk_map tid1 ~f:(fun v_wrapped ->
                  match v_wrapped with
                  | None -> Tid.Set.singleton tid2
                  | Some set_blk2_idxs ->  Tid.Set.union set_blk2_idxs (Tid.Set.singleton tid2))),
             (* this should never exist *)
             Tid.Map.update blk_varmap tid1
               ~f:(fun cur_map ->
                   match cur_map with
                   | None -> Tid.Map.singleton tid2 v_map
                   | Some m -> Tid.Map.add_exn m ~key:tid2 ~data:v_map)
           | None ->
             blk_map, blk_varmap) in
      let blk_map, blk_varmap = BFS.fold inner_evaluator (blk_map, blk_varmap) cfg2 in
      blk_map, blk_varmap) in
  BFS.fold evaluator (blk_map, blk_varmap) cfg1

(* Compare a label.t with tid comparisons only *)
let compare_lbl_tid_only (graph : Tid.t Tid.Map.t) (lbl1 : Label.t)
    (lbl2 : Label.t) : bool =
  match lbl1, lbl2 with
  | Direct tid1, Direct tid2 ->
    let tid_mapped = Tid.Map.find_exn graph tid1 in
    Tid.equal tid_mapped tid2
  | Indirect _, Indirect _ -> true
  | _, _ -> false


(* Compare a jmp with tid comparisons only *)
let compare_jmp_tid_only (graph : Tid.t Tid.Map.t) (jmp1 : jmp term) (jmp2 : jmp term) =
  match Jmp.kind jmp1, Jmp.kind jmp2 with
  | Goto label1, Goto label2 -> compare_lbl_tid_only graph label1 label2
  | Call call1, Call call2 ->
    begin
      let match_returns =
        match Call.return call1, Call.return call2 with
        | Some label1, Some label2 -> compare_lbl_tid_only graph label1 label2
        | None, None -> true
        | _, _ -> false in
      let match_targets =
        compare_lbl_tid_only graph (Call.target call1) (Call.target call2) in
      match_returns && match_targets
    end
  | Ret label1, Ret label2 -> compare_lbl_tid_only graph label1 label2
  | Int (_, tid1), Int (_, tid2) ->
    let tid_mapped = Tid.Map.find_exn graph tid1 in
    Tid.equal tid_mapped tid2
  | _, _ -> false

(* Check that the two blocks has matching TIDs in jumps. *)
let compare_blk_tid_only (graph : Tid.t Tid.Map.t)
    (blk1 : blk term) (blk2 : blk term) : bool =
  let jmps1 = Term.enum jmp_t blk1 |> Sequence.to_list in
  let jmps2 = Term.enum jmp_t blk2 |> Sequence.to_list in
  match List.zip jmps1 jmps2 with
  | Core_kernel.List.Or_unequal_lengths.Unequal_lengths -> false
  | Core_kernel.List.Or_unequal_lengths.Ok z ->
    List.for_all z ~f:(fun (j1, j2) -> compare_jmp_tid_only graph j1 j2)

(* Check that the graph from tid to tid has matching TIDs in jumps. *)
let check_isomorphism
    (graph : Tid.t Tid.Map.t)
    (tid_to_blk1 : (blk term) Tid.Map.t)
    (tid_to_blk2 : (blk term) Tid.Map.t) : bool
  =
  Tid.Map.for_alli graph
    ~f:(fun ~key:tid1 ~data:tid2 ->
        let blk1 = Tid.Map.find_exn tid_to_blk1 tid1 in
        let blk2 = Tid.Map.find_exn tid_to_blk2 tid2 in
        compare_blk_tid_only graph blk1 blk2)

(* Checks that two maps from variable to variable can be merged.
   This means that they do not have contradictory definitions
   for the same key. *)
let merge_maps (merged_map : Var.t Var.Map.t) (new_map : Var.t Var.Map.t) : (Var.t Var.Map.t) option =
  let new_merged_map = Var.Map.merge merged_map new_map
      ~f:(fun ~key:_key v ->
          match v with
          | `Left v1 -> Some v1
          | `Right v2 -> Some v2
          | `Both (v1, v2) -> if Var.equal v1 v2 then Some v1 else None)
  in
  let get_keys = (fun m -> Var.Map.keys m |> Var.Set.of_list) in
  let expected_len = Var.Set.union (get_keys merged_map) (get_keys new_map) |> Var.Set.length in
  let actual_len = Var.Map.keys new_merged_map |> List.length in
  match actual_len = expected_len with
  | false -> None
  | true -> Some new_merged_map

(* Given
   - a [candidate_map] of sub1 block tids to a set of sub2 block tids that
     sub1 is syntactically equal to (barring TIDs in jmps)
   - a [used_set] of already mapped to sub_1 TIDS
   - a [node_stack] of sub1 blks that have not yet been mapped to,
   - a partial mapping, denoted [graph], from sub1 tids to sub2 tids,
   - a mapping, [tid_to_blk1] from sub1 tids to sub1 blks,
   - a mapping, [tid_to_blk2] from sub2 tids to sub2 blks,
   - a map from (tid1, tid2) to a variable mapping [var_maps] generated by that pair of blocks
   - [merged_map], a map built out of block-wise maps corresponding
     to the current partial mapping
   - returns a isomorphism from tids in sub1 to tids in sub2 if they exist *)
let rec get_isomorphism
    (candidate_map : Tid.Set.t Tid.Map.t) (used_set : Tid.Set.t)
    (node_stack : (blk term) list) (graph : Tid.t Tid.Map.t)
    (tid_to_blk1 : (blk term) Tid.Map.t) (tid_to_blk2 : (blk term) Tid.Map.t)
    (var_maps : ((Var.t Var.Map.t) Tid.Map.t) Tid.Map.t) (merged_map : Var.t Var.Map.t) :
  (Tid.t Tid.Map.t) option  =
  let node = List.hd node_stack in
  match node with
  | None ->
    if check_isomorphism graph tid_to_blk1 tid_to_blk2
    then Some graph
    else None
  | Some node ->
    let tid = Term.tid node in
    match Tid.Map.find candidate_map tid with
    | Some possible_nodes ->
      let candidate_nodes = Tid.Set.diff possible_nodes used_set in
      Tid.Set.find_map candidate_nodes
        ~f:(fun tid_mapped_to ->
            let used_set = Tid.Set.union used_set (Tid.Set.singleton tid_mapped_to) in
            (* cannot be empty *)
            let node_stack = List.tl_exn node_stack in
            let graph = Tid.Map.update graph tid ~f:(fun _ -> tid_mapped_to) in
            Tid.Map.find var_maps tid >>=
            fun tid1_map -> Tid.Map.find tid1_map tid_mapped_to >>=
            fun new_map ->
            merge_maps merged_map new_map >>=
            fun merged_map ->
            get_isomorphism candidate_map used_set node_stack
              graph tid_to_blk1 tid_to_blk2 var_maps merged_map)
    | None -> None

(* Gets all syntactically equal blocks between the two subs,
   Checks if it is possible to construct a mapping between
   the two sets of blocks that matches in control flow. *)
let subs_to_isomorphism (sub1: Sub.t) (sub2 : Sub.t) : (Tid.t Tid.Map.t) option =
  let cfg1, cfg2 = Sub.to_cfg sub1, Sub.to_cfg sub2 in
  let tid_to_blk1, tid_to_blk2 = get_node_map cfg1, get_node_map cfg2 in
  let tid_map, var_maps = compare_blocks_syntax sub1 sub2 in
  let used_set = Tid.Set.empty in
  let node_stack = Tid.Map.data tid_to_blk1 in
  let node2_stack = Tid.Map.data tid_to_blk2 in
  let graph = Tid.Map.empty in
  (* short circuit if we already know that the length does not match *)
  if (List.length node_stack) = (List.length node2_stack) then
    get_isomorphism tid_map used_set node_stack graph tid_to_blk1 tid_to_blk2 var_maps Var.Map.empty >>|
    fun iso -> printf "Blocks are syntactically equal! Not performing WP analysis.\nUNSAT!\n"; iso
  else None
