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

module Word_ops = Cbat_word_ops
module Utils = Cbat_vsa_utils
module Clp = Cbat_clp
module FinSet = Cbat_fin_set

type clp = Clp.t
type fset = FinSet.t

(* INVARIANT: Clps have cardinality > Utils.fin_set_size
   INVARIANT: FinSets have cardinality <= Utils.fin_set_size
*)
type t = Clp of Clp.t | FinSet of FinSet.t [@@deriving bin_io, sexp, compare]
type idx = int

let of_list ~width l : t =
  if List.length l > !Utils.fin_set_size
  then Clp (Clp.of_list ~width l)
  else FinSet (FinSet.of_list ~width l)

let singleton w = FinSet (FinSet.singleton w)

let lift_consume (f_clp : clp -> 'a) (f_fs : fset -> 'a) : t -> 'a = function
  | Clp p -> f_clp p
  | FinSet s -> f_fs s

let clp_of_finset fs : clp =
  let width = FinSet.bitwidth fs in
  FinSet.iter fs
  |> Clp.of_list ~width

let finset_of_clp p : fset =
  let width = Clp.bitwidth p in
  Clp.iter p
  |> FinSet.of_list ~width

let as_clp = function
  | Clp p -> p
  | FinSet s -> clp_of_finset s

(* TODO: rename to canonize? *)
let bound_set_size = function
  | Clp p -> if Word_ops.gt_int (Clp.cardinality p) !Utils.fin_set_size
    then Clp p
    else FinSet (finset_of_clp p)
  | FinSet s -> if Word_ops.gt_int (FinSet.cardinality s) !Utils.fin_set_size
    then Clp (clp_of_finset s)
    else FinSet s

let lift_binop (f_clp : clp -> clp -> clp) (f_fs : fset -> fset -> fset)
    t1 t2 : t = bound_set_size @@ match t1, t2 with
  | Clp p1, Clp p2 -> Clp (f_clp p1 p2)
  | FinSet s1, FinSet s2 -> FinSet (f_fs s1 s2)
  | Clp p, FinSet s -> Clp (f_clp p (clp_of_finset s))
  | FinSet s, Clp p -> Clp (f_clp (clp_of_finset s) p)

let lift_unop (f_clp : clp -> clp) (f_fs : fset -> fset) : t -> t = function
  | Clp p -> bound_set_size @@ Clp (f_clp p)
  | FinSet s -> bound_set_size @@ FinSet (f_fs s)

let of_clp (p : clp) : t = bound_set_size (Clp p)

let bitwidth = lift_consume Clp.bitwidth FinSet.bitwidth

let cardinality = lift_consume Clp.cardinality FinSet.cardinality

let min_elem = lift_consume Clp.min_elem FinSet.min_elem
let max_elem = lift_consume Clp.max_elem FinSet.max_elem
let min_elem_signed = lift_consume Clp.min_elem_signed FinSet.min_elem_signed
let max_elem_signed = lift_consume Clp.max_elem_signed FinSet.max_elem_signed
let nearest_pred w = lift_consume (Clp.nearest_pred w) (FinSet.nearest_pred w)
let nearest_succ w = lift_consume (Clp.nearest_succ w) (FinSet.nearest_succ w)
let splits_by = lift_consume Clp.splits_by FinSet.splits_by

let elem w = lift_consume (Clp.elem w) (FinSet.elem w)
let iter = lift_consume Clp.iter FinSet.iter

let equal t1 t2 : bool = match t1, t2 with
  | Clp p1, Clp p2 -> Clp.equal p1 p2
  | FinSet s1, FinSet s2 -> FinSet.equal s1 s2
  | Clp _, FinSet _
  | FinSet _, Clp _ -> false

let overlap t1 t2 : bool = match t1, t2 with
  | Clp p1, Clp p2 -> Clp.overlap p1 p2
  | FinSet s1, FinSet s2 -> FinSet.overlap s1 s2
  | Clp p, FinSet s
  | FinSet s, Clp p -> FinSet.overlap_generic (module Clp) s p

let union = lift_binop Clp.union FinSet.union
(* The definition below is more precise than
   'lift_binop Clp.intersection FinSet.intersection'
*)
let intersection (t1 : t) (t2 : t) : t =
  assert(bitwidth t1 = bitwidth t2);
  match t1, t2 with
  | Clp p1, Clp p2 -> Clp (Clp.intersection p1 p2)
  | FinSet s1, FinSet s2 -> FinSet (FinSet.intersection s1 s2)
  | Clp p, FinSet s
  | FinSet s, Clp p -> FinSet (FinSet.intersect_generic (module Clp) s p)

let add = lift_binop Clp.add FinSet.add
let sub = lift_binop Clp.sub FinSet.sub
let mul = lift_binop Clp.mul FinSet.mul
let div = lift_binop Clp.div FinSet.div
let sdiv = lift_binop Clp.sdiv FinSet.sdiv
let modulo = lift_binop Clp.modulo FinSet.modulo
let smodulo = lift_binop Clp.smodulo FinSet.smodulo
let arshift = lift_binop Clp.arshift FinSet.arshift
let rshift = lift_binop Clp.rshift FinSet.rshift
let lshift = lift_binop Clp.lshift FinSet.lshift
let logand : t -> t -> t = lift_binop Clp.logand FinSet.logand
let logor = lift_binop Clp.logor FinSet.logor
let logxor = lift_binop Clp.logxor FinSet.logxor

let lnot = lift_unop Clp.lnot FinSet.lnot
let neg = lift_unop Clp.neg FinSet.neg

let extract ?hi ?lo = lift_unop (Clp.extract ?hi ?lo) (FinSet.extract ?hi ?lo)
let cast c sz = lift_unop (Clp.cast c sz) (FinSet.cast c sz)

let concat = lift_binop Clp.concat FinSet.concat

let is_top = lift_consume Clp.is_top (fun _ -> false)
let is_bottom = lift_consume (fun _ -> false) (Fn.compose Word.is_zero FinSet.cardinality)

(* Lattice implementation *)
let precedes t1 t2 : bool = match t1, t2 with
  | Clp p1, Clp p2 -> Clp.precedes p1 p2
  | FinSet s1, FinSet s2 -> FinSet.precedes s1 s2
  | Clp _, FinSet _ -> false
  | FinSet s, Clp p -> Clp.precedes (clp_of_finset s) p

let widen_join t1 t2 : t = bound_set_size @@
  Clp (Clp.widen_join (as_clp t1) (as_clp t2))

let join = union
let meet = intersection
let bottom i = FinSet (FinSet.bottom i)
let top i = bound_set_size @@ Clp (Clp.top i)

let get_idx = lift_consume Clp.get_idx FinSet.get_idx

let pp ppf = lift_consume (Clp.pp ppf) (FinSet.pp ppf)

(* helper function *)
let finset_clp_dist nearest s p =
  let open Monads.Std.Monad.Option.Syntax in
  FinSet.iter s
  |> List.fold ~init:None ~f:begin fun mmin w ->
    let mnxt = nearest w p in
    let mdist = Option.map mnxt ~f:(fun nxt -> Word.sub nxt w) in
    Option.value_map ~default:mdist mmin ~f:(fun m ->
        Option.value_map mdist ~default:(!!m) ~f:(fun dist ->
            if Word.(<=) m dist then !!m else !!dist))
  end

