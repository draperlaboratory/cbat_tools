open !Core_kernel
open Bap.Std
open Graphlib.Std
open Base__Option.Monad_infix

(* some of these pattern matchings are massive; we don't want fragile warnings *)
[@@@warning "-4"]

module H = Bap.Std.Graphs.Ir
module J = Graphlib.To_ocamlgraph (H)
module BFS = Graph.Traverse.Bfs (J)
module TidSet = Set.Make(Tid)

module TidMap = Map.Make(Tid)
module VarMap = Map.Make(Var)
module VarSet = Set.Make(Var)
module TidTupleMap = Map.Make(struct type t = Tid.t * Tid.t [@@deriving sexp, compare] end)

type varToVarMap = Var.t VarMap.t

(* replaces the real variables with indices with only their base *)
let rec strip_indices (e : Exp.t) : Exp.t =
  let open Bap.Std.Bil.Types in
  match e with
  | Load (exp1, exp2, endian, size) ->
    Load (strip_indices exp1, strip_indices exp2, endian, size)
  | Store (exp1, exp2, exp3, endian, size) ->
    Store (strip_indices exp1, strip_indices exp2, strip_indices exp3, endian, size)
  | BinOp (binop, exp1, exp2) ->
    BinOp (binop, strip_indices exp1, strip_indices exp2)
  | UnOp (unop, exp1) -> UnOp (unop, strip_indices exp1)
  | Var v -> Var (Var.base v)
  | Bap.Std.Bil.Types.Int w -> Bap.Std.Bil.Types.Int w
  | Cast (cast, i, exp1) -> Cast (cast, i, strip_indices exp1)
  | Let (var, exp1, exp2) ->
    Let (Var.base var, strip_indices exp1, strip_indices exp2)
  | Unknown (s, typ) -> Unknown (s, typ)
  | Ite (exp1, exp2, exp3) ->
    Ite (strip_indices exp1, strip_indices exp2, strip_indices exp3)
  | Extract (i, j, exp) -> Extract (i, j, strip_indices exp)
  | Concat (exp1, exp2) -> Concat (strip_indices exp1, strip_indices exp2)

(* Perform variable lookup in map. BOTH variables must be virtual.
   If they are not, then fail and return None.*)
let map_var (vmap : varToVarMap)
    (v1 : Var.t) (v2 : Var.t) : (varToVarMap * Var.t) option  =
  match VarMap.find vmap v1 with
  (* if not found in map, add to map *)
  | None ->
    (* if is virtual, do mapping *)
    if Var.is_virtual v1 && Var.is_virtual v2 then
      (VarMap.add_exn vmap ~key:v1 ~data:v2, v2) |> Some
      (* if is physical register, just return original variable *)
    else Some (vmap, v1)
  (* if found in map, return what is found *)
  | Some v_found -> (vmap, v_found) |> Some

(* maps all virtual variables from e1 to their analagous variable within vmap;
 * if variable not in vmap, is added to vmap from e2
 *  returns None if cannot map variables because subs do not match in structure *)
let rec sub_exp (vmap : varToVarMap)
    (e1 : Exp.t) (e2 : Exp.t) : (varToVarMap * Exp.t) option =
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

(* gets the block associated with a node in the graph *)
let get_label (a: Bap.Std.Graphs.Ir.Node.t) : blk term =
  Bap.Std.Graphs.Ir.Node.label a

(* compares two defs; returns the updated varmap if they match; returns None
 * if do not match*)
let compare_def (def1 : def term) (def2 : def term) (vmap_orig : varToVarMap)
  : varToVarMap option  =
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

(* compares label based on only expression*)
let compare_lbl (lbl1 : label) (lbl2 : label) (map : varToVarMap) : varToVarMap option =
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
   - jmp1 and jmp2 match in all Exp.ts contained within
*)
let compare_jmp jmp1 jmp2 map =
  match Jmp.kind jmp1, Jmp.kind jmp2 with
  | Goto label1, Goto label2 -> compare_lbl label1 label2 map
  | Call call1, Call call2 ->
    begin
      (* TODO assert equality *)
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
let compare_phis phis1 phis2 map =
  if List.length phis1 > 0 || List.length phis2 > 0 then None
  else Some map

(* Check that all defs in two lists match. *)
let compare_defs (defs1 : (def term) list)
    (defs2 : (def term) list) (map : varToVarMap) : varToVarMap option =
  match List.zip defs1 defs2 with
  | Core_kernel.List.Or_unequal_lengths.Unequal_lengths -> None
  | Core_kernel.List.Or_unequal_lengths.Ok z ->
    List.fold z ~init:(Some map)
      ~f:(fun (map_wrap) (d1, d2) ->
          match map_wrap with
          | None -> None
          | Some map -> compare_def d1 d2 map)

(* Check that all jmps in a list match in expression and structure. *)
let compare_jmps jmps1 jmps2 map =
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
  compare_defs (Term.enum def_t blk1 |> Sequence.to_list) (Term.enum def_t blk2 |> Sequence.to_list) map >>=
  fun map -> compare_jmps (Term.enum jmp_t blk1 |> Sequence.to_list) (Term.enum jmp_t blk2 |> Sequence.to_list) map >>=
  fun map -> compare_phis (Term.enum phi_t blk1 |> Sequence.to_list) (Term.enum phi_t blk2 |> Sequence.to_list) map

(* Iterate through all reachable nodes in each cfg
 *  and generate a map from tid to blk.*)
let get_node_maps
    (cfg1 : Bap.Std.Graphs.Ir.t)
    (cfg2 : Bap.Std.Graphs.Ir.t) : ((blk term) TidMap.t) * ((blk term) TidMap.t) =
  let acc = fun ele tid_map ->
    let tid = Term.tid (get_label ele) in
    TidMap.change tid_map tid ~f:(fun _ -> Some (get_label ele)) in
  let tid1_map =
    BFS.fold acc TidMap.empty cfg1 in
  let tid2_map =
    BFS.fold acc TidMap.empty cfg2 in
  tid1_map, tid2_map

(* compares a sub to another sub; returns a map from index into sub 1
 * to the set of sub2 indices that it is syntactically equal to
 * and a map from (indx_sub1, indx_sub2) to var maps*)
let compare_blocks (sub1: Sub.t) (sub2 : Sub.t) : (TidSet.t TidMap.t) * (varToVarMap TidTupleMap.t) =
  let cfg1, cfg2 = Sub.to_cfg sub1, Sub.to_cfg sub2 in
  (* blk1 indx -> set{blk2 indxs} *)
  let blk_map = TidMap.empty in
  (* blk1 indx, blk2 indx -> varmap *)
  let blk_varmap = TidTupleMap.empty in
  let evaluator = (fun (node1 : Bap.Std.Graphs.Ir.Node.t) (blk_map, blk_varmap) ->
      let blk1 = get_label node1 in
      let tid1 = Term.tid (get_label node1) in
      let inner_evaluator =
        (fun (node2 : Bap.Std.Graphs.Ir.Node.t) (blk_map, blk_varmap) ->
           let blk2 = get_label node2 in
           let tid2 = Term.tid blk2 in
           let v_map = VarMap.empty in
           match compare_block blk1 blk2 v_map with
           | Some v_map ->
             (TidMap.change blk_map tid1 ~f:(fun v_wrapped ->
                  match v_wrapped with
                  | None -> TidSet.singleton tid2 |> Some
                  | Some set_blk2_idxs ->  TidSet.union set_blk2_idxs (TidSet.singleton tid2) |> Some)),
             (* this should never exist *)
             TidTupleMap.add_exn blk_varmap ~key:((tid1, tid2)) ~data:v_map
           | None ->
             blk_map, blk_varmap) in
      let blk_map, blk_varmap = BFS.fold inner_evaluator (blk_map, blk_varmap) cfg2 in
      blk_map, blk_varmap) in
  BFS.fold evaluator (blk_map, blk_varmap) cfg1

(* compare the label but only draw comparisons with tid *)
let compare_lbl_tid_only graph lbl1 lbl2 : bool=
  match lbl1, lbl2 with
  | Direct tid1, Direct tid2 ->
    let tid_mapped = TidMap.find_exn graph tid1 in
    Tid.equal tid_mapped tid2
  | Indirect _, Indirect _ -> true
  | _, _ -> false


(* compare the jmp but with tid comparisons only *)
let compare_jmp_tid_only graph jmp1 jmp2 =
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
    let tid_mapped = TidMap.find_exn graph tid1 in
    Tid.equal tid_mapped tid2
  | _, _ -> false

let compare_blk_tid_only graph blk1 blk2 : bool =
  let jmps1 = Term.enum jmp_t blk1 |> Sequence.to_list in
  let jmps2 = Term.enum jmp_t blk2 |> Sequence.to_list in
  match List.zip jmps1 jmps2 with
  | Core_kernel.List.Or_unequal_lengths.Unequal_lengths -> (* TODO exception *) false
  | Core_kernel.List.Or_unequal_lengths.Ok z ->
    List.for_all z ~f:(fun (j1, j2) -> compare_jmp_tid_only graph j1 j2)

(* checks that the proposed mapping is actually isomorphic *)
let check_isomorphism
    (graph : Tid.t TidMap.t)
    (tid_to_blk1 : (blk term) TidMap.t)
    (tid_to_blk2 : (blk term) TidMap.t) : bool
  =
  TidMap.for_alli graph
    ~f:(fun ~key:tid1 ~data:tid2 ->
        let blk1 = TidMap.find_exn tid_to_blk1 tid1 in
        let blk2 = TidMap.find_exn tid_to_blk2 tid2 in
        compare_blk_tid_only graph blk1 blk2)

let merge_maps (merged_map : varToVarMap) (new_map : varToVarMap) : varToVarMap option =
  let new_merged_map = VarMap.merge merged_map new_map
      ~f:(fun ~key:_key v ->
          match v with
          | `Left v1 -> Some v1
          | `Right v2 -> Some v2
          | `Both (v1, v2) -> if Var.equal v1 v2 then Some v1 else None)
  in
  let get_keys = (fun m -> VarMap.keys m |> VarSet.of_list) in
  let expected_len = VarSet.union (get_keys merged_map) (get_keys new_map) |> VarSet.length in
  let actual_len = VarMap.keys new_merged_map |> List.length in
  match actual_len = expected_len with
    false -> None
  | true -> Some new_merged_map

let rec get_isomorphism
    (candidate_map : TidSet.t TidMap.t) (used_set : TidSet.t)
    (node_stack : (blk term) list) (graph : Tid.t TidMap.t)
    (tid_to_blk1 : (blk term) TidMap.t) (tid_to_blk2 : (blk term) TidMap.t)
    (var_maps : varToVarMap TidTupleMap.t) (merged_map : varToVarMap) :
  (Tid.t TidMap.t) option  =
  let node = List.hd node_stack in
  match node with
  | None ->
    if check_isomorphism graph tid_to_blk1 tid_to_blk2
    then Some graph
    else None
  | Some node ->
    let tid = Term.tid node in
    match TidMap.find candidate_map tid with
    | Some possible_nodes ->
      let candidate_nodes = TidSet.diff possible_nodes used_set in
      TidSet.find_map candidate_nodes
        ~f:(fun tid_mapped_to ->
            let used_set = TidSet.union used_set (TidSet.singleton tid_mapped_to) in
            (* cannot be empty *)
            let node_stack = List.tl_exn node_stack in
            let graph = TidMap.update graph tid ~f:(fun _ -> tid_mapped_to) in
            (* TODO change this to a map lookup *)
            TidTupleMap.find var_maps (tid, tid_mapped_to) >>=
            fun new_map ->
            merge_maps merged_map new_map >>=
            fun merged_map ->
            get_isomorphism candidate_map used_set node_stack
              graph tid_to_blk1 tid_to_blk2 var_maps merged_map)
    | None -> None

let get_length cfg : int =
  let f = ( fun node acc ->
      let lbl = get_label node in
      let def_len = Term.enum def_t lbl |> Sequence.to_list |> List.length in
      let jmp_len = Term.enum jmp_t lbl |> Sequence.to_list |> List.length in
      acc + def_len + jmp_len
    ) in
  BFS.fold f 0 cfg

let exist_isomorphism (sub1: Sub.t) (sub2 : Sub.t) : bool =
  let cfg1, cfg2 = Sub.to_cfg sub1, Sub.to_cfg sub2 in
  printf "\nLENGTH IS: %d\n" (get_length cfg1);
  let tid_to_blk1, tid_to_blk2 = get_node_maps cfg1 cfg2 in
  (* the variable mappings on a per-block basis are not actually used *)
  let tid_map, var_maps = compare_blocks sub1 sub2 in
  let _ = printf "PERCENTAGE_IDENTICAL_BLOCKS_IS: %.4f\n" (((List.length (TidMap.keys tid_map)) |> float_of_int) /. ((List.length (TidMap.keys tid_to_blk1)) |> float_of_int)) in
  (* List.iter (TidMap.keys tid_map) ~f:(fun key -> printf "TID MAP: %s\n" (Tid.to_string key)) ; *)
  let used_set = TidSet.empty in
  let node_stack = TidMap.data tid_to_blk1 in
  let node2_stack = TidMap.data tid_to_blk2 in
  let graph = TidMap.empty in
  printf "BLOCK LENGTH: %d\n" (List.length node_stack);
  (* short circuit if we already know that the length does not match *)
  if (List.length node_stack) = (List.length node2_stack) then
    match get_isomorphism tid_map used_set node_stack graph tid_to_blk1 tid_to_blk2 var_maps VarMap.empty with
    | None -> false
    | Some _x ->
      printf "Blocks are syntactically equal! Not performing WP analysis.\nUNSAT!\n"; true
  else false
