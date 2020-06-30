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

include Bap.Std
module W = Word
module Option = Core_kernel.Option
open Cbat_vsa_utils

(* Computes w1 * w2 at the sum of their bitwidths. This ensures that
   the result cannot overflow. Note that this operation is size-polymorphic
*)
let mul_exact (w1 : word) (w2 : word) : word =
  let sz1 = W.bitwidth w1 in
  let sz2 = W.bitwidth w2 in
  let sz_ext = sz1 + sz2 in
  let w1_ext = W.extract_exn ~hi:(sz_ext - 1) w1 in
  let w2_ext = W.extract_exn ~hi:(sz_ext - 1) w2 in
  W.mul w1_ext w2_ext

let add_exact (w1 : word) (w2 : word) : word =
  let sz1 = W.bitwidth w1 in
  let sz2 = W.bitwidth w2 in
  let sz_ext = 1 + max sz1 sz2 in
  let w1_ext = W.extract_exn ~hi:(sz_ext - 1) w1 in
  let w2_ext = W.extract_exn ~hi:(sz_ext - 1) w2 in
  W.add w1_ext w2_ext

let succ_exact (w : word) : word =
  let width = W.bitwidth w in
  W.succ @@ W.extract_exn ~hi:width w

let lshift_exact (w : word) (i : int) : word =
  let width = i + W.bitwidth w in
  let wi = W.of_int ~width i in
  let w' = W.extract_exn ~hi:(width - 1) w in
  W.lshift w' wi

(* Calculates the greatest common divisor of two words
   such that the result is not greater than the inputs.
*)
let bounded_gcd (w1 : word) (w2 : word) : word =
  let width = W.bitwidth w1 in
  assert (width = W.bitwidth w2);
  if W.is_zero w1 then w2
  else if W.is_zero w2 then w1
  else W.gcd_exn w1 w2

(* Performs an unsigned division that rounds updwards instead of downwards. *)
let cdiv a b : word = if W.is_zero (W.modulo a b)
    then W.div a b else W.succ (W.div a b)

let is_one (w : word) : bool = W.is_zero (W.pred w)

(* Computes the least solution x_0 to the linear Diophantine equation
   ax + by = c such that 0 <= x_0. All arguments must be the same size.
   Outputs a word of the same size as the inputs
*)
let bounded_diophantine (a : word) b c : (word * word) option =
  let size = W.bitwidth a in
  assert (size = W.bitwidth b);
  assert (size = W.bitwidth c);
  let zero = W.zero size in
  if W.is_zero c then Some (zero, zero)
  else if W.is_zero a && W.is_zero b then None
  else if W.is_zero a then
    if W.is_zero (W.modulo c b) then Some (zero, W.div c b) else None
  else if W.is_zero b then
    if W.is_zero (W.modulo c a) then Some (W.div c a, zero) else None
  else
    (* we have that ax + by = d. Note that, assuming that gcdext
       uses the Euclidean algorithm, x and y will satisfy
       |x| <= b/2 and |y| <= a/2. Thus, they will fit within
       the same number of bits, even when signed. Note, however,
       that operations including arbitrary unsigned values of the
       same size may not operate as expected.
    *)
    let d, unsigned_x, unsigned_y = W.gcdext_exn a b in
    let signed_x = W.signed unsigned_x in
    let signed_y = W.signed unsigned_y in
    let gcd_quotient = W.div c d in
    (* these have width size * 2 *)
    let signed_x0 = W.signed (mul_exact signed_x gcd_quotient) in
    let signed_y0 = W.signed (mul_exact signed_y gcd_quotient) in
    if not (W.is_zero (W.modulo c d)) then None
    else
      (* All solutions have the form (x + k  * b/d, y - k * a/d).
         again assuming that gcdext uses the euclidian algorithm,
         this produces x and y with minimum |x| and minimum |y|
      *)
      Some (W.extract_exn ~hi:(size-1) signed_x0,
            W.extract_exn ~hi:(size-1) signed_y0)

(* Computes the smallest (positive) n : word and m : int such that
   w = 2^m * n via binary search
*)
let factor_2s (w : word) : word * int =
  let rec factor_help (hi : int) (lo : int) : int =
    if hi = lo then hi else
      let mid = (hi + lo) / 2 in
      let lo_part = W.extract_exn ~hi:mid ~lo w in
      if W.is_zero lo_part then factor_help hi (mid + 1)
      else factor_help mid lo
  in
  let width = W.bitwidth w in
  let lo = factor_help (width - 1) 0 in
  (* make sure the result has the same width as the input *)
  let hi = width - 1 + lo in
  W.extract_exn ~hi ~lo w, lo


(* Computes the position of the leading 1-bit via binary search *)
let lead_1_bit (w : word) : int option =
  let rec lead_help (hi : int) (lo : int) : int option =
    let open Monads.Std.Monad.Option.Syntax in
    Option.some_if (hi >= lo) () >>= fun _ ->
    if hi = lo then !!hi else
    let mid = (hi + lo) / 2 in
    let hi_part = W.extract_exn ~hi ~lo:(mid + 1) w in
    if W.is_zero hi_part then lead_help mid lo
    else lead_help hi (mid + 1)
  in
  if W.is_zero w then None else lead_help ((W.bitwidth w) - 1) 0

let count_initial_1s (w : word) : int = snd @@ factor_2s @@ W.lnot w

let min w1 w2 : word = if W.(<) w1 w2 then w1 else w2
let max w1 w2 : word = if W.(<) w1 w2 then w2 else w1

(* returns the word 2^i with bitwidth width *)
let dom_size ?width (i : int) : word =
  let width = Option.value ~default:(i + 1) width in
  let one = W.one width in
  let i_wd = W.of_int ~width i in
  W.lshift one i_wd

(* Returns the word of the given bitwidth with the smallest
   integer difference from the word w.
*)
let cap_at_width ~width (w : word) : word =
  let w_width = W.bitwidth w in
  if w_width <= width then W.extract_exn ~hi:(width - 1) w else
    (* Compute the largest width-bit number, stored in w_width bits *)
    let max_w = W.pred @@ dom_size ~width:w_width width in
    let res_val = min max_w w in
    W.extract_exn ~hi:(width - 1) res_val

(* extends the word by a single high bit *)
let add_bit (w : word) : word =
  W.extract_exn ~hi:(W.bitwidth w) w

let endian_string : W.endian -> string = function
  | BigEndian -> "BE"
  | LittleEndian -> "le"

let gt_int (w : word) (i : int) : bool =
  W.(>) w (W.of_int i ~width:(W.bitwidth w))

let lt_int (w : word) (i : int) : bool =
  W.(<) w (W.of_int i ~width:(W.bitwidth w))
