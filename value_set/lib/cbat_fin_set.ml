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

open !Core_kernel
open Bap.Std

(* Included to implement create more easily;
   This indicates that create may not be the right interface
*)
module WordSet = Cbat_wordset_intf
module WSet = Set.Make_binable(Word)

type t =  WSet.t * int [@@deriving bin_io, sexp]
type idx = int



let of_list ~width l = WSet.of_list l, width
let singleton w =
  let bw = Word.bitwidth w in
  WSet.singleton w, bw

let bitwidth (_, bw) : int = bw

let cardinality (s, width) : word =
  WSet.length s
  |> Word.of_int ~width

let signed (s, bw) =
  let signed_s = WSet.map s ~f:Word.signed in
  (signed_s, bw)

let min_elem = Fn.compose WSet.min_elt fst
let max_elem = Fn.compose WSet.max_elt fst

let max_elem_signed t = max_elem (signed t)
let min_elem_signed t = min_elem (signed t)

let elem w (s, bw) : bool =
  assert(Word.bitwidth w = bw);
  WSet.mem s w

let iter = Fn.compose WSet.elements fst

let lift ?(width=fun x->x) (f : WSet.t -> WSet.t) (s, bw : t) : t = (f s, width bw)

let lift2 ?(width=fun w1 w2-> assert(w1 = w2); w1)
    (f : WSet.t -> WSet.t -> WSet.t)
    (s1, bw) (s2, bw') : t =
  f s1 s2, width bw bw'

let lift2_pred (f : WSet.t -> WSet.t -> bool)
    (s1, bw) (s2, bw') : bool =
  assert(bw = bw');
  f s1 s2

let lift_unop (op : word -> word) : WSet.t -> WSet.t = WSet.map ~f:op

let lift_binop (op : word -> word -> word)
    s1 s2 : WSet.t =
  WSet.fold_right s1 ~init:WSet.empty ~f:begin fun w1 init ->
    WSet.fold_right s2 ~init ~f:begin fun w2 s ->
      WSet.add s (op w1 w2)
    end
  end

let lift_binop_signed (op : word -> word -> word)
    s1 s2 : WSet.t =
  WSet.fold_right s1 ~init:WSet.empty ~f:begin fun w1 init ->
    WSet.fold_right s2 ~init ~f:begin fun w2 s ->
      WSet.add s (op (Word.signed w1) (Word.signed w2))
    end
  end

let equal = lift2_pred WSet.equal

let overlap (s1, bw) (s2, bw') : bool =
  assert(bw = bw');
  not @@ WSet.is_empty @@ WSet.inter s1 s2

let union = lift2 WSet.union
let intersection = lift2 WSet.inter

let add = lift2 (lift_binop Word.add)
let sub = lift2 (lift_binop Word.sub)
let mul = lift2 (lift_binop Word.mul)
(* TODO: how to handle division-by-zero? *)
let div = lift2 (lift_binop Word.div)
let sdiv = lift2 (lift_binop_signed Word.div)
let modulo = lift2 (lift_binop Word.modulo)
let smodulo = lift2 (lift_binop_signed Word.modulo)

let arshift = lift2 ~width:Fn.const (lift_binop Word.arshift)
let rshift  = lift2 ~width:Fn.const (lift_binop Word.rshift)
let lshift = lift2 ~width:Fn.const (lift_binop Word.lshift)

let logand : t -> t -> t = lift2 (lift_binop Word.logand)
let logor : t -> t -> t = lift2 (lift_binop Word.logor)
let logxor : t -> t -> t = lift2 (lift_binop Word.logxor)

let lnot = lift (lift_unop Word.lnot)
let neg = lift (lift_unop Word.neg)

let nearest_pred w (s, bw) : word option =
  assert(Word.bitwidth w = bw);
  WSet.fold s ~init:None ~f:(fun mmin w' ->
      let diff = Word.sub w w' in
      Option.value_map mmin ~default:(Some diff) ~f:(fun m ->
          if Word.(<=) m diff then Some m else Some diff))

let nearest_succ (i : word) (s : t) : word option =
  Option.map ~f:Word.lnot (nearest_pred (Word.lnot i) (lnot s))

(* Determines whether the set is spaced by a multiple of w
   when considered as an interval in the range [0..2^sz)
*)
let splits_by (s, _ : t) (w : word) : bool =
  let rec map2_shortest ~f l1 l2 = match l1,l2 with
    | [], _
    | _, [] -> []
    | e1::l1', e2::l2' -> f e1 e2 :: (map2_shortest ~f l1' l2') in
  let elems = WSet.elements s
              |> List.sort ~cmp:Word.compare in
  let open Monads.Std.Monad.Option.Syntax in
  Option.value ~default:true begin
    List.tl elems >>| fun tl ->
    map2_shortest tl elems ~f:Word.sub
    |> List.for_all ~f:(fun diff -> Word.is_zero (Word.modulo diff w))
  end

(* TODO: should we be burying errors like this? this indicates
   that a change of the interface might be appropriate
*)
let extract ?hi ?(lo=0) =
  let new_bw w =
    let hi = Option.value ~default:(w-1) hi in
    hi - lo + 1 in
  lift ~width:new_bw @@ lift_unop (Word.extract_exn ?hi ~lo)

let cast ct (sz : int) : t -> t =
  lift ~width:(Fn.const sz) @@ lift_unop (Bil.Apply.cast ct sz)

let concat = lift2 ~width:(fun w1 w2 -> w1 + w2) (lift_binop Word.concat)

(* Lattice implementation *)
let precedes = lift2_pred (fun s1 s2 -> WSet.is_subset s1 ~of_:s2)
let widen_join _ _ = failwith "widen not implemented; usually impractical"
let join = union
let meet = intersection
let bottom bw = WSet.empty, bw
(* TODO: implement top and error on high values; used for some small bitwidths *)
let top _ = failwith "top not implemented; usually impractical"
let get_idx = snd

let pp ppf (s, _) =
  Format.fprintf ppf "@[{@ ";
  Set.iter s ~f:(Format.fprintf ppf "%a@ " Word.pp);
  Format.fprintf ppf "}@]"

let compare (s1, bw1) (s2, bw2) =
  if bw1 < bw2 then -1
  else if bw1 > bw2 then 1
  else WSet.compare s1 s2

(* Actions of a FinSet on a WordSet from a potentially different module *)

let intersect_generic (type ws) (module WS : WordSet.S with type t = ws)
    (s, bw : t) (s' : ws) : t =
  assert(WS.bitwidth s' = bw);
  let keep_set = WSet.filter s ~f:(fun w -> WS.elem w s') in
  keep_set, bw

let overlap_generic (type ws) (module WS : WordSet.S with type t = ws)
    (s, bw : t) (s' : ws) : bool =
  let s, _ = intersect_generic (module WS) (s,bw) s' in
  not @@ WSet.is_empty s
