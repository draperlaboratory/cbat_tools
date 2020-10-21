open !Core_kernel
open Bap.Std
open Graphlib.Std
open Base__Option.Monad_infix

[@@@warning "-4"]

module H = Bap.Std.Graphs.Ir
module J = Graphlib.To_ocamlgraph (H)
module BFS = Graph.Traverse.Bfs (J)
module IntSet = Set.Make(Int)
module VarMap = Map.Make(Var)
module IntMap = Map.Make(Int)
module IntTupleMap = Map.Make(struct type t = int * int [@@deriving sexp, compare] end)

(* wrapper to remove indices in case var.base doesn't do the trick *)
let remove_indices_from_var (v : Var.t) : Var.t =
  Var.base v

(* replaces the real variables with their base *)
let rec strip_indices (e : Exp.t) : Exp.t =
  let open Bap.Std.Bil.Types in
  match e with
  | Load (exp1, exp2, endian, size) -> Load (strip_indices exp1, strip_indices exp2, endian, size)
  | Store (exp1, exp2, exp3, endian, size) -> Store (strip_indices exp1, strip_indices exp2, strip_indices exp3, endian, size)
  | BinOp (binop, exp1, exp2) -> BinOp (binop, strip_indices exp1, strip_indices exp2)
  | UnOp (unop, exp1) -> UnOp (unop, strip_indices exp1)
  | Var v -> Var (remove_indices_from_var v)
  | Bap.Std.Bil.Types.Int w -> Bap.Std.Bil.Types.Int w
  | Cast (cast, i, exp1) -> Cast (cast, i, strip_indices exp1)
  | Let (var, exp1, exp2) -> Let (remove_indices_from_var var, strip_indices exp1, strip_indices exp2)
  | Unknown (s, typ) -> Unknown (s, typ)
  | Ite (exp1, exp2, exp3) -> Ite (strip_indices exp1, strip_indices exp2, strip_indices exp3)
  | Extract (i, j, exp) -> Extract (i, j, strip_indices exp)
  | Concat (exp1, exp2) -> Concat (strip_indices exp1, strip_indices exp2)

(* perform variable lookup in map. TODO more about if they're virtual *)
let map_var (vmap : Var.t VarMap.t) (v1 : Var.t) (v2 : Var.t) : (Var.t VarMap.t * Var.t) option  =
  printf "\nIN SUB_EXP, encoutnered: Var 1: %s Var 2: %s\n" (Var.to_string v1) (Var.to_string v2);
  match VarMap.find vmap v1 with
  (* if not found in map, add to map *)
  | None ->
    (* if is virtual, do mapping *)
    if Var.is_virtual v1 && Var.is_virtual v2 then
      (VarMap.add_exn vmap ~key:v1 ~data:v2, v2) |> Some
      (* if is physical register, just return original variable *)
    else v1
  (* if found in map, return what is found *)
  | Some v_found -> (vmap, v_found) |> Some

(* maps all virtual variables from e1 to their analagous variable with vmap;
 * if variable not in vmap, is added to vmap from e2
 *  returns none if cannot map variables because subs do not match in structure *)
let rec sub_exp (vmap : Var.t VarMap.t) (e1 : Exp.t) (e2 : Exp.t) : (Var.t VarMap.t * Exp.t) option =
  let open Bap.Std.Bil.Types in
  match e1, e2 with
  | Load (exp1_bin1, exp2_bin1, endian, size), Load (exp1_bin2, exp2_bin2, _, _) ->
    sub_exp vmap exp1_bin1 exp1_bin2 >>=
    fun (vmap, exp1_bin1) -> sub_exp vmap exp2_bin1 exp2_bin2 >>|
    fun (vmap, exp2_bin1) -> vmap, Load (exp1_bin1, exp2_bin1, endian, size)
  | Store (exp1_bin1, exp2_bin1, exp3_bin1, endian, size), Store (exp1_bin2, exp2_bin2, exp3_bin2, _, _) ->
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
  | Bap.Std.Bil.Types.Int w, Bap.Std.Bil.Types.Int _ -> Some (vmap, Bap.Std.Bil.Types.Int w)
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
  | Ite (exp1_bin1, exp2_bin1, exp3_bin1), Ite (exp1_bin2, exp2_bin2, exp3_bin2) ->
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

(* compares two defs; returns the updated varmap if they match; returns none
 * if do not match*)
let compare_def (def1 : def term) (def2 : def term) (vmap_orig : Var.t VarMap.t)
  : (Var.t VarMap.t) option  =
  let var1_orig, var2 =
    Bap.Std.Bil.Types.Var (Def.lhs def1), Bap.Std.Bil.Types.Var (Def.lhs def2) in
  let var1_orig, var2 = strip_indices var1_orig, strip_indices var2 in
  sub_exp vmap_orig var1_orig var2 >>= fun (vmap, var1) ->
  let lhs_is_equal = Exp.equal var1 var2 in
  let _ = printf "\nLHS EQUAL: %b defn lhs_orig: \n%s\n, mapped %s \n second: %s\n" lhs_is_equal (Exp.to_string var1_orig) (Exp.to_string var1) (Exp.to_string var2) in
  let rhs1_orig, rhs2 = Def.rhs def1, Def.rhs def2 in
  let rhs1_orig, rhs2 = strip_indices rhs1_orig, strip_indices rhs2 in
  sub_exp vmap rhs1_orig rhs2 >>= fun (vmap, rhs1) ->
  let rhs_is_equal = Exp.equal rhs1 rhs2 in
  let _ = printf "\nRHS EQUAL: %b defn rhs_orig: \n%s\n, mapped %s\n second: %s\n" rhs_is_equal (Exp.to_string rhs1_orig) (Exp.to_string rhs1) (Exp.to_string rhs2) in
  if rhs_is_equal && lhs_is_equal then
    Some vmap
  else None

let compare_lbl (lbl1 : label) (lbl2 : label) (map : Var.t VarMap.t) : (Var.t VarMap.t) option =
  match lbl1, lbl2 with
  | Direct _tid1, Direct _tid2 -> Printf.printf "A direct jump to a tid.\n" ; Some map
  | Indirect exp1, Indirect exp2 ->
    let exp1, exp2 = strip_indices exp1, strip_indices exp2 in
    sub_exp map exp1 exp2 >>=
    fun (map, exp1) ->
    if Exp.equal exp1 exp2 then
      Some map
    else None
  | _, _ -> Printf.printf "NOT EQUAL lbls"; None

let compare_jmp jmp1 jmp2 map =
  match Jmp.kind jmp1, Jmp.kind jmp2 with
  | Goto label1, Goto label2 -> Printf.printf "A jump to a block.\n%!" ; compare_lbl label1 label2 map
  | Call _call1, Call _call2 -> Printf.printf "A jump to a subroutine.\n%!" ; Some map
  | Ret label1, Ret label2 -> Printf.printf "Return to a block.\n%!" ; compare_lbl label1 label2 map
  | Int (_code, _tid1), Int (_code2, _tid2) -> Printf.printf "An interrupt.\n%!" ; Some map
  | _, _ -> Printf.printf "NOT EQUAL jmp types" ; None

let compare_phis phis1 phis2 map =
  if List.length phis1 > 0 || List.length phis2 > 0 then false, map
  else true, map

(* compare a list of defs TODO change signature to option *)
let compare_defs (defs1 : (def term) list) (defs2 : (def term) list) (map : Var.t VarMap.t) : bool * (Var.t VarMap.t) =
  match List.zip defs1 defs2 with
  | Core_kernel.List.Or_unequal_lengths.Unequal_lengths -> false, map
  | Core_kernel.List.Or_unequal_lengths.Ok z -> List.fold z ~init:(true, map)
                                                  ~f:(fun (b, map) (d1, d2) ->
                                                      match compare_def d1 d2 map with
                                                      | Some map_new -> b, map_new
                                                      | None -> printf "GOT A FALSE IN COMPARE_DEFS" ; false, map)

let compare_jmps jmps1 jmps2 map =
  match List.zip jmps1 jmps2 with
  | Core_kernel.List.Or_unequal_lengths.Unequal_lengths -> false, map
  | Core_kernel.List.Or_unequal_lengths.Ok z -> List.fold z ~init:(true, map)
                                                  ~f:(fun (b, map) (j1, j2) ->
                                                      match compare_jmp j1 j2 map with
                                                      | Some map_new -> b, map_new
                                                      | None -> printf "GOT A FALSE JMP"; false, map)

(* compare block TODOchange signature to option *)
let compare_block blk1 blk2 map =
  let eq_def, map = compare_defs (Term.enum def_t blk1 |> Sequence.to_list) (Term.enum  def_t blk2 |> Sequence.to_list) map in
  let eq_jmp, map = compare_jmps (Term.enum jmp_t blk1 |> Sequence.to_list) (Term.enum jmp_t blk2 |> Sequence.to_list) map in
  let eq_phi, map = compare_phis (Term.enum phi_t blk1 |> Sequence.to_list) (Term.enum phi_t blk2 |> Sequence.to_list) map in
  eq_def && eq_phi && eq_jmp, map

(* compares a sub to another sub; returns a map from index into sub 1
 * to the set of sub2 indices that it is syntactically equal to
 * and a map from (indx_sub1, indx_sub2) to var maps*)
let compare_blocks (sub1: Sub.t) (sub2 : Sub.t) : (IntSet.t IntMap.t) * ((Var.t VarMap.t) IntTupleMap.t)=
  let cfg1, cfg2 = Sub.to_cfg sub1, Sub.to_cfg sub2 in
  (* blk1 indx -> set{blk2 indxs} *)
  let blk_map = IntMap.empty in
  (* blk1 indx, blk2 indx -> varmap *)
  let blk_varmap = IntTupleMap.empty in
  let evaluator = (fun node1 (blk_map, blk_varmap, k) ->
      let inner_evaluator =
        (fun node2 (blk_map, blk_varmap, i) ->
           let j = i + 1 in
           let v_map = VarMap.empty in
           let eq, v_map = compare_block (get_label node1) (get_label node2) v_map in
           if eq then
             (IntMap.change blk_map k ~f:(fun v_wrapped ->
                  match v_wrapped with
                  | None -> IntSet.singleton i |> Some
                  | Some set_blk2_idxs ->  IntSet.union set_blk2_idxs (IntSet.singleton i) |> Some)),
             (* this should never exist *)
             IntTupleMap.add_exn blk_varmap ~key:((k, i)) ~data:v_map, j
           else
             blk_map, blk_varmap, j) in
      let blk_map, blk_varmap, _ = BFS.fold inner_evaluator (blk_map, blk_varmap, 0) cfg2 in
      blk_map, blk_varmap, k+1
    )
  in
  let blk_map, blk_varmap, _  = BFS.fold evaluator (blk_map, blk_varmap, 0) cfg1 in
  blk_map, blk_varmap

(* performs the overarching comparison for exact syntactic equality between subs*)
let cmp_overall (sub1 : Sub.t) (sub2 : Sub.t) : bool =
  let cfg1, cfg2 = Sub.to_cfg sub1, Sub.to_cfg sub2 in
  let seen_set = IntSet.empty in
  let v_map = VarMap.empty in
  let evaluator = (fun node1 (does_match_so_far, seen_set, v_map) ->
      match does_match_so_far with
      | false -> false, seen_set, v_map
      | true ->
        let inner_evaluator =
          (fun node2 (found_match, seen_set, v_map, i) ->
             let j = i + 1 in
             match found_match with
             | true -> true, seen_set, v_map, i
             | false ->
               (* if already matched, then don't consider again *)
               if IntSet.exists seen_set ~f:(fun a -> a = i) then false, seen_set, v_map, j
               (* otherwise, perform comparison *)
               else
                 let eq, v_map_updated = compare_block (get_label node1) (get_label node2) v_map in
                 if eq then
                   eq, IntSet.union seen_set (IntSet.singleton i), v_map_updated, j
                 else
                   eq, seen_set, v_map, j) in
        let r, s, m, _ = BFS.fold inner_evaluator (false, seen_set, v_map, 0) cfg2 in
        r, s, m
    )
  in
  let r, _seen_set, _v_map = BFS.fold evaluator (true, seen_set, v_map) cfg1 in
  r
