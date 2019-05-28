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

open Bap.Std
include Cbat_vsa_utils

module W = Word
module Option = Core_kernel.Option
module Sexp = Core_kernel.Sexp
module List = Core_kernel.List

open !Cbat_word_ops

(* A CLP {base; step; card} represents the following set:
   {base + n * step | 0 <= n < cardn}.  Note that since cardn can be 2^sz, it
   is stored in a sz+1 bit word. If step * cardn >= 2^sz in Z, then the CLP is
   conservatively approximated as cardn = 2^sz. This simplifies to the following
   set: {(base + n * step) % sz | n in Nat}. We refer to these as 'infinite' CLPs.
   TODO: is there a better name than infinite CLPs?

   Invariants:
   W.bitwidth base = W.bitwidth step
   W.bitwidth cardn = (W.bitwidth base) + 1

   Note that for an arbitrary CLP, cardn is an approximation of its cardinality.
   Its actual cardinality could be less since the CLP may overlap itself.

   Note: module-internal code should be careful of any operations that treat
   the CLP as an interval from its beginning to its end since this is likely to break
   equality between certain infinite CLPs (specifically those that are and aren't
   finite).

*)
type t = {base : word; step : word; cardn : word}
[@@deriving bin_io]

(* Creates a new CLP that ranges from base to base + step * (pred num)
   in increments of size step. Note that num = 0 represents the empty
   set and that this function approximates progressions that wrap
   around themselves.
   'width' is the desired bitwidth of the CLP.
   Defaults to the bitwidth of base.
   Step and cardn default such that [create n] represents the set {n}
   Note that canonization depends on these defaults.
*)
let create ?(width : int option) ?(step = W.b1) ?(cardn = W.b1) base : t =
  let width = Option.value ~default:(W.bitwidth base) width in
  (* truncates or extends the word to the appropriate size *)
  let fit = W.extract_exn ~hi:(width - 1) in
  (* While fit produces the correct behavior for the step (modulo the bitwidth),
     a sufficiently large cardinality is instead equivalent to the maximum
     cardinality at the given width.
  *)
  let cardn = Cbat_word_ops.cap_at_width ~width:(width + 1) cardn in
  {base = fit base; step = fit step; cardn}

let singleton w = create w

let bitwidth (p : t) : int = W.bitwidth p.base

(* helper function; constructs a CLP from its lower bound, upper bound
   and step. Note that if the following equation does not hold, then
   the upper bound will not be an element of the resultant CLP:
   exists i such that upper = lower + step*i
   TODO: check; there are some places this could be used
*)
let cardn_from_bounds base step e : word =
  let width = W.bitwidth base in
  assert(W.bitwidth step = width);
  (* Compute the cardinality. Integer division (floor) produces
     the correct behavior.
  *)
  if W.is_zero step then W.one (width + 1) else
    let div_by_step = W.div (W.sub e base) step in
    (* extract adds an extra bit at the high end so that
       the call to succ never wraps to 0.
    *)
    W.succ (W.extract_exn ~hi:width div_by_step)

(* helper function; computes the minimum/canonical CLP to represent
   the set of words of the form b + sn for any integer n
   Note: returns a canonized result
*)
let infinite (b, s) : t =
  let width = W.bitwidth b in
  assert (width = W.bitwidth s);
  if W.is_zero s then create b
  else let div, twos = factor_2s s in
    let step = W.div s div in
    let base = W.modulo b step in
    let cardn = dom_size ~width:(width + 1) (width - twos) in
    {base; step; cardn}

(* helper function; determines whether a given CLP represents
   a set of the form {(b + s*i) % z | i in Nat}
   Note that in the terminology of this module, a set may be both
   infinite and finite. A set is both iff e + s = b % z where
   e is the end of the CLP and z is its bitwidth.
*)
let is_infinite p : bool =
  let width = bitwidth p in
  let ds = dom_size ~width:(2*width + 1) width in
  let mul = mul_exact p.cardn p.step in
  W.(>=) mul ds

(* outputs a canonized CLP *)
let bottom (width : int) : t =
  assert(width > 0);
  create ~width W.b0 ~cardn:W.b0

let top (i : int) : t =
  assert(i > 0);
  let zero = W.zero i in
  let one = W.one i in
  infinite (zero, one)

(* helper function; converts a CLP into a unique representation.
   A canonized infinite CLP has the following properties:
   (elem i (b,s)) /\ i < j < i + s => not (elem j (b,s))
   b < s
*)
let canonize (p : t) : t =
  let szInt = bitwidth p in
  let two = W.of_int ~width:(szInt + 1) 2 in
  (* Each CLP with step s and cardinality c such that 0 < sc <= 2^szInt
     2 < c < 2^szInt has a single representation
  *)
  (* A cardinality of 0 represents the empty set *)
  if W.is_zero p.cardn then bottom szInt
  (* Either a nonzero cardinality and step of 0 or a cardinality of 1
     represents a singleton set.
  *)
  else if W.is_zero p.step || is_one p.cardn then create p.base ~step:W.b0
  (* Cardinality 2 sets can be flipped; we represent them in the order
     where the end is greater than the beginning.
  *)
  else if W.(=) p.cardn two then
    let e = W.add p.base p.step in
    if W.(>=) e p.base then p
    else create e ~step:(W.neg p.step) ~cardn:two
  (* If p.cardn steps traverse the full domain, we approximate
     with an infinite CLP. In other words, all cardinalities c
     such that c*p.step <= 2^szIn are treated equivalently.
  *)
  else if is_infinite p then infinite(p.base, p.step)
  else p

(* Returns the cardinality of p as a sz+1 width word,
   where sz is the bitwidth of p.
*)
let cardinality (p : t) : word = (canonize p).cardn

(* helper function; computes the last point in a finite CLP.
   Note that this function may return misleading results for an
   infinite CLP. The result will be a point on the CLP, but is in
   no way an 'end' since an infinite CLP has no notion of end.
*)
let finite_end (p : t) : word option =
  let width = bitwidth p in
  let n = W.extract_exn ~hi:(width - 1) p.cardn in
  if W.is_zero p.cardn then None
  else Some (W.add p.base (W.mul p.step (W.pred n)))

(* Note: this function is fully precise *)
let lnot (p : t) : t =
  (* We use the finite end even in the infinite case since it is always
     guaranteed to be some point on the CLP and for the infinite CLP,
     any point works as the base.
  *)
  Option.value_map ~default:(bottom (bitwidth p)) (finite_end p)
    ~f:(fun e -> {base = W.lnot e; step = p.step; cardn = p.cardn})

(* Returns a list containing all of the elements represented by
   the input CLP.
*)
let iter (p : t) : word list =
  let rec iter_acc b s n acc =
    if W.is_zero n then acc
    else let n' = W.pred n in
      iter_acc (W.add b s) s n' (b :: acc) in
  let p' = canonize p in
  iter_acc p'.base p'.step p'.cardn []

(*  computes the closest element of p that precedes
   i, i.e. the first element reached by starting from i and decreasing.
   Assumes that the inputs have the same bitwidth.
*)
let nearest_pred (i : word) (p : t) : word option =
  assert(bitwidth p = W.bitwidth i);
  let open Monads.Std.Monad.Option.Syntax in
  (* If finite_end returns none, the CLP is empty *)
  finite_end p >>= fun e ->
  if W.is_zero p.step then !!(p.base)
  else
    (* We translate i and p by -p.base to avoid wrapping over 0 *)
    let diff = W.sub i p.base in
    let rm = W.modulo diff p.step in
    (* Compute the end of p translated by -p.base *)
    let end' = W.sub e p.base in
    if is_infinite p then !!(W.sub i rm)
    else if W.(>=) diff end' then !!(W.add end' p.base) else
      (* The remainder is the difference between i and the result*)
      !!(W.sub i rm)

(* helper function;
   Some (nearest_inf_pred w b p) = nearest_pred w (infinite b p) *)
let nearest_inf_pred (w : word) (base : word) (step : word) : word =
  if W.is_zero step then base else
    let diff = W.sub w base in
    let rm = W.modulo diff step in
    W.sub w rm

let nearest_succ (i : word) (p : t) : word option =
  Option.map ~f:W.lnot (nearest_pred (W.lnot i) (lnot p))

(* helper function;
   Some (nearest_inf_succ w b p) = nearest_succ w (infinite b p) *)
let nearest_inf_succ (w : word) (base : word) (step : word) : word =
  W.lnot (nearest_inf_pred (W.lnot w) (W.lnot base) step)

let max_elem (p : t) : word option =
  let max_wd = W.ones (bitwidth p) in
  nearest_pred max_wd p

let min_elem (p : t) : word option =
  let min_wd = W.zero (bitwidth p) in
  nearest_succ min_wd p

(** The max elem of a signed CLP is going to be the nearest precedessor
    of (2^w / 2) - 1, where [w] is the bit-width of the words in the CLP.

    For instance, if we assume [w = 3] (3-bits in each word), a
    circle with the numbers 0 through 7, when signed, becomes a
    circle with the numbers -4 through 3. So the maximum element in the
    CLP is going to be the nearest predecessor to 3.

    We can get (2^w / 2) by getting the [dom_size] of [w - 1]. E.g.,
    the domain size when [w = 3] is 8, but half of that is the same as 
    the domain size when [w = 2], namely 4. 

    Note that the max element this function returns is not signed (like
    all BAP words). To see the signed value, use [W.signed word].*)
let max_elem_signed (p : t) : word option =
  let width = bitwidth p in
  let half_way_point = dom_size ~width:width (width - 1) in
  let max_dom_elem = W.pred half_way_point in
  nearest_pred max_dom_elem p

(** The min elem of a signed CLP is going to be the nearest successor
    of (2^w / 2). Note that the returned word is unsigned. To see
    the signed value, use [W.signed word]. *)
let min_elem_signed (p : t) : word option =
  let width = bitwidth p in
  let half_way_point = dom_size ~width:width (width - 1) in
  nearest_succ half_way_point p

let splits_by (p : t) (w : word) : bool =
  let p = canonize p in
  let divides a b = W.is_zero (W.modulo b a) in
  let open Monads.Std.Monad.Option.Syntax in
  Option.value ~default:true begin
    min_elem p >>= fun min_p ->
    finite_end p >>= fun e ->
    if W.is_zero p.step then !!true else
      (* The Clp contains more than one element *)
      !!(divides w p.step &&
         (* if it wraps 0, w must divide the gap *)
         (W.(=) p.base min_p ||
          divides w (W.sub e p.base)))
  end

let min_separation (p : t) : word option =
  let p = canonize p in
  let open Monads.Std.Monad.Option.Syntax in
  finite_end p >>= fun e ->
  if W.(=) p.base e then None
  else !!(min p.step (min (W.sub p.base e) (W.sub e p.base)))

(* Decides membership in the set represented by the CLP *)
let elem (i : word) (p : t) : bool =
  assert (W.bitwidth i = bitwidth p);
  match nearest_pred i p with
  | None -> false
  | Some j -> W.(=) i j

(* helper function; checks whether two CLPs have the same size
   and if so, outputs that size
*)
let get_and_check_sizes (p1 : t) (p2 : t) : int =
  let sz1 = bitwidth p1 in
  let sz2 = bitwidth p2 in
  let err_str = Printf.sprintf "Input CLPs of different sizes: %i and %i" sz1 sz2 in
  if sz1 <> sz2 then raise (Invalid_argument err_str);
  sz1

(* Checks whether a given CLP is the top element of the lattice.
   Works by checking whether the step is coprime with the size of
   the domain since the domain can be seen as a cyclic group
   of the form (Z_(2^n), +).
*)
let is_top (p : t) : bool = canonize p = top (bitwidth p)

(* decides whether the input represents the empty set *)
let is_bottom (p : t) : bool = W.is_zero p.cardn

(* helper function; checks whether the first infinite progression
   is a subprogression (i.e. aligned and with a step that contains
   at least as many factors of 2) of the second.
*)
let subprogression (b1,s1) (b2,s2) : bool =
  if W.is_zero s1 then
    (* return true if b1 is in the second progression. In other words,
       if any number of s2-sized steps gets from b1 to b2
    *)
    let diff = W.sub b2 b1 in
    let rem = W.modulo diff s2 in
    W.is_zero rem
  else if W.is_zero s2 then W.is_zero s1 && b1 = b2
  else
    let coprime1, _ = factor_2s s1 in
    let coprime2, _ = factor_2s s2 in
    let powTwo1 = W.div s1 coprime1 in
    let powTwo2 = W.div s2 coprime2 in
    let bRoot1 = W.modulo b1 powTwo2 in
    let bRoot2 = W.modulo b2 powTwo2 in
    W.(>=) powTwo1 powTwo2 && W.(=) bRoot1 bRoot2

(* determines whether two CLPs are equivalent. Much faster than subset. *)
let equal (p1 : t) (p2 : t) : bool =
  let _ = get_and_check_sizes p1 p2 in
  canonize p1 = canonize p2

let unwrap (p : t) : t =
  let open Monads.Std.Monad.Option.Syntax in
  Option.value ~default:(bottom (bitwidth p)) begin
    min_elem p >>= fun base ->
    max_elem p >>= fun e ->
    let step = p.step in
    let cardn = cardn_from_bounds base step e in
    !!{base; step; cardn}
  end

let unwrap_signed (p : t) : t =
  let open Monads.Std.Monad.Option.Syntax in
  Option.value ~default:(top (bitwidth p)) begin
    min_elem_signed p >>= fun base ->
    max_elem_signed p >>= fun e ->
    let step = p.step in
    let cardn = cardn_from_bounds base step e in
    !!{base; step; cardn}
  end

(* helper function; takes two inclusive circular intervals and returns
   the smallest interval that is a superset of the two. Assumes that
   all inputs have the same bitwidth.
*)
let interval_union (a1,b1) (a2,b2) : (word * word) =
  let szInt = W.bitwidth a1 in
  (* we translate both intervals by a1 so that one interval starts at 0 *)
  let b1' = W.sub b1 a1 in
  let a2' = W.sub a2 a1 in
  let b2' = W.sub b2 a1 in
  let zero = W.zero szInt in
  (* If b2' < a2', then the second interval wraps over the zero point and
     a1 is in the interval (a2,b2). Also, if a2' (and so also b2') is in
     the first interval, then the two wrap fully around the circle.
  *)
  if W.(>=) b1' a2' && W.(<) b2' a2' then (b1, W.pred b1)
  (* If a2' and b2' are both between 0 and b1' then a2 and b2 are between
     a1 and b1. Since the case above has been ruled out, the first interval
     subsumes the second.
  *)
  else if W.(>=) b1' a2' && W.(>=) b1' b2' then (a1, b1)
  (* By excluding the above two cases, we know that b2' is not in (0,b1').
     Since a2' is, the intervals overlap and stretch from a1 to b2.
  *)
  else if W.(>=) b1' a2' then (a1, b2)
  (* In all following cases, a2' is not within (0, b1'). If b2' is, then
     the intervals overlap in the other direction and stretch from a2 to b1.
  *)
  else if W.(<) b2' b1' then (a2, b1)
  (* In all following cases, neither a2' or b2' are in (0, b1'). If b2' < a2'
     then (a2', b2') wraps around 0, so it must subsume (0, b1).
  *)
  else if W.(<) b2' a2' then (a2, b2)
  (* Otherwise, there are 2 gaps and we include the smaller one. *)
  else if W.(>) (W.sub a2' b1') (W.sub zero b2') then (a2,b1)
  else (a1, b2)


(* helper function; moves a CLP around the number circle without
   changing its cardinality or step size.
*)
let translate (p : t) i : t =
  {base = W.add p.base i; step = p.step; cardn = p.cardn}


(* helper function; Given two progressions with a start and a step size,
   computes the largest step size that contains both points and each
   point that they step to. Equivalenently, computes the step size of
   the union of the two infinite CLPs. Assumes that the two CLPs
   have the same bitwidth. We take the gcd of the step sizes and
   the (shortest) distance between the bases. Thus, the resulting
   step, when started from either base, will eventually reach all
   points in both progressions in the same order as the original CLPs.
*)
let common_step (b1,s1) (b2,s2) : word =
  let bDiff = if W.(>) b1 b2 then W.sub b1 b2 else W.sub b2 b1 in
  if W.is_zero s1 then bounded_gcd s2 bDiff
  else if W.is_zero s2 then bounded_gcd s1 bDiff
  else let gcdS = (bounded_gcd s1 s2) in
    bounded_gcd gcdS bDiff

(* defines a partial order on CLPs in terms of the sets that
   they represent.
*)
let subset (p1 : t) (p2 : t) : bool =
  let width = get_and_check_sizes p1 p2 in
  (* canonization allows us to treat the CLPs as finite *)
  let p1 = canonize p1 in
  let p2 = canonize p2 in
  (* We translate both CLPs such that one of them starts at 0
     in order to simplify our reasoning.
  *)
  let nb2 = W.neg p2.base in
  let p1 = translate p1 nb2 in
  let p2 = translate p2 nb2 in
  (* One finite CLP is a subset of another if its
     step is a multiple of the other's step, its bounds
     are within the bounds of the other, and they
     overlap on at least one point.
     Note that since singleton CLPs can have any step,
     the step condition does not need to be checked.
  *)
  let end1 = finite_end p1 in
  let end2 = finite_end p2 in
  begin match end1, end2 with
    | None, _ -> true
    | Some _, None -> false
    | Some e1, Some e2 ->
      (* p1 is a subset of p2 if its bounds are within p2's bounds
         and p2's step covers all elements in their union.
      *)
      let in_bounds = W.(<=) e1 e2 && W.(<=) p1.base e2 in
      let step_and_overlap = W.(=) (common_step (p1.base,p1.step) (W.zero width, p2.step)) p2.step in
      let singleton_elem = is_one p1.cardn && elem p1.base p2 in
      singleton_elem || (in_bounds && step_and_overlap)
  end

(* To find the start of the intersection, we need to find the
   first point base with the following constraints:
     base = p1.base (mod p1.step)
     base = p1.base (mod p2.step)
     base in [p1.base, e1]
     base in [p2.base, e2]
   where e1 and e2 are the ends of p1 and p2 respectively.
   We translate both CLPs by -b1 to get the following constraints
     base - p1.base = 0 (mod p1.step)
     base - p1.base = p2.base - p1.base (mod p2.step)
     base - p1.base <= e1 - p1.base
     base - p1.base >= p2.base - p1.base
     base - p1.base <= e2 - p1.base
   Let x' denote x - p1.base for all x. We equivalently have the following:
     exists j. base' = j * p1.step
     exists k. base' = p2.base' + k * p2.step
     p2.base' <= base' <= min(e1', e2')
   Thus, base' is (j0 * p1.step) if j0 is the least solution
   to the linear diophantine equation j * p1.step - k * p2.step = p2.base' and,
   in the finite case, p2.base' <= base' <= min(e1', e2')
*)
let intersection (p1 : t) (p2 : t) : t =
  let width = get_and_check_sizes p1 p2 in
  let bot = bottom width in
  (* Canonize to ensure that the CLPs may be treated as finite in most cases
     and simplify other handling
  *)
  let p1 = canonize p1 in
  let p2 = canonize p2 in
  (* ensure that p1.base >= p2.base so that neither end crosses p1.base *)
  let p1, p2 = if W.(>=) p1.base p2.base then p1, p2 else p2, p1 in
  (* Translate the CLPs so that p1 starts at 0 *)
  let translation = p1.base in
  let translated_p1 = translate p1 (W.neg p1.base) in
  let translated_p2 = translate p2 (W.neg p1.base) in
  let p1, p2 = translated_p1, translated_p2 in
  let p1_infinite = is_infinite p1 in
  let p2_infinite = is_infinite p2 in
  let open Monads.Std.Monad.Option.Syntax in
  Option.value ~default:bot begin
    finite_end p1 >>= fun e1 ->
    finite_end p2 >>= fun e2 ->
    match bounded_lcm p1.step p2.step with
    | Some step ->
      bounded_diophantine p1.step p2.step p2.base >>= fun (x,_) ->
      (* the result is the first point on p1 that is also on the infinite CLP
         approximation of p2. Due to the translation of the CLPs, this is the
         least possible value (before translating back) that can inhabit the
         intersection.
      *)
      let base = W.mul x p1.step in
      (* e1 and e2 are meaningful iff p1 and p2 respectively are non-infinite.
         We therefore guard their use so that when either argument is
         infinite, we compute the proper end.
      *)
      let minE = if p1_infinite then e2
        else if p2_infinite then e1
        else min e1 e2 in
      (* If the least possible value in resulting set is greater than the
         maximum possible value, then the set is empty. This does not apply
         when p1 is infinite since sometimes the base of p2 (and therefore
         the result) can wrap backwards over 0.
      *)
      Option.some_if (W.(<=) base minE) () >>= fun _ ->
      let cardn = cardn_from_bounds base step minE in
      !!(create base ~step ~cardn)
    | None ->
      (* If there is no bounded LCM then s1 or s2 are 0. In other words,
         one of the inputs is a singleton. Thus the intersection is either
         equal to the singleton or empty.
      *)
      if W.is_zero p2.step then
        Option.some_if (elem p2.base p1) () >>= fun _ ->
        !!(create p2.base)
      else
        Option.some_if (elem p1.base p2) () >>= fun _ ->
        !! (create p1.base)
        (* whatever the result, we translate it by the original p1.base
           to make up for the translation at the start.
        *)
  end |> (fun p -> translate p translation)

(* Computes whether there exists any element in both CLPs
 *)
let overlap (p1 : t) (p2 : t) : bool = not (is_bottom (intersection p1 p2))


(* Approximates the union of the two abstracted sets.
   Input CLPs should have the same bitwidth.
*)
let union (p1 : t) ( p2 : t) : t =
  (* CLPs canonized so that they may be treated as finite *)
  let p1 = canonize p1 in
  let p2 = canonize p2 in
  (* If either CLP is empty, return the other one *)
  Option.value_map ~default:p2 (finite_end p1) ~f:begin fun e1 ->
    Option.value_map ~default:p1 (finite_end p2) ~f:begin fun e2 ->
      (* Compute the bounds of the interval that contains this CLP *)
      let base, newE = interval_union (p1.base, e1) (p2.base, e2) in
      let step = common_step (p1.base, p1.step) (p2.base, p2.step) in
      (* if the common step is 0, then base = newE *)
      let cardn = cardn_from_bounds base step newE in
      create base ~step ~cardn
    end
  end

let add (p1 : t) (p2 : t) : t =
  let sz = get_and_check_sizes p1 p2 in
  (* If either CLP is empty, return bottom *)
  Option.value_map ~default:(bottom sz) (finite_end p1) ~f:begin fun e1 ->
    Option.value_map ~default:(bottom sz) (finite_end p2) ~f:begin fun e2 ->
        (* if either CLP has step 0 it is a singleton and
           we simply add its value to each element of the other
           This case is computed exactly.
        *)
      if W.is_zero p1.step || is_one p1.cardn then translate p2 p1.base
      else if W.is_zero p2.step || is_one p2.cardn then translate p1 p2.base
      else if is_infinite p1 || is_infinite p2 then
        infinite (W.add p1.base p2.base, bounded_gcd p1.step p2.step)
      else
        (* Translate p1 by -b1 and p2 by -b2 so that they each
           start at 0. We can just add b1 + b2 at the end to
           reverse this.
        *)
        let e1' = W.sub e1 p1.base in
        let e2' = W.sub e2 p2.base in
        let e' = W.add e1' e2' in
        let base = W.add p1.base p2.base in
        let step = bounded_gcd p1.step p2.step in
        (* If the sum wraps around, then it encompasses the full circle *)
        if W.(<) e' e1' then infinite (base, step)
        else let cardn = cardn_from_bounds (W.zero sz) step e' in
          create base ~step ~cardn
    end
  end

(* Note: this function is fully precise *)
let neg (p : t) : t =
  (* We use the finite end even in the infinite case since it is always
     guaranteed to be some point on the CLP and for the infinite CLP,
     any point works as the base.
  *)
  Option.value_map ~default:(bottom (bitwidth p)) (finite_end p)
    ~f:(fun e -> {base = W.neg e; step = p.step; cardn = p.cardn})

let sub (p1: t) (p2 : t) : t = add p1 (neg p2)

let mul (p1 : t) (p2 : t) : t =
  let sz = get_and_check_sizes p1 p2 in
  (* If either CLP is empty, return bottom *)
  Option.value_map ~default:(bottom sz) (finite_end p1) ~f:begin fun e1 ->
    Option.value_map ~default:(bottom sz) (finite_end p2) ~f:begin fun e2 ->
      (* if either CLP  is a singleton, we simply
         multiply each element of the other by its value
         This case is computed exactly.
      *)
      if W.is_zero p1.step || is_one p1.cardn then
        let base = W.mul p2.base p1.base in
        let step = W.mul p2.step p1.base in
        create base ~step ~cardn:p2.cardn
      else if W.is_zero p2.step || is_one p2.cardn then
        let base = W.mul p1.base p2.base in
        let step = W.mul p1.step p2.base in
        create base ~step ~cardn:p1.cardn
      else
        let base = mul_exact p1.base p2.base in
        let e'_exact = mul_exact e1 e2 in
        let step = bounded_gcd (mul_exact p1.base p2.step)
            (bounded_gcd (mul_exact p2.base p1.step)
               (mul_exact p1.step p2.step)) in
        let end_diff = W.sub e'_exact base in
        let div_res = W.div end_diff step in
        let cardn = W.succ @@ add_bit div_res in
        if is_infinite p1 ||is_infinite p2 then
          let fit = W.extract_exn ~hi:(sz - 1) in
          infinite (fit base, fit step)
        else create ~width:sz base ~step ~cardn
    end
  end


(* helper function;
   TODO: describe
   TODO: should be in word_ops.ml???
   TODO: check!!!
 *)
let lead_1_bit_run (w : word) ~hi ~lo : int =
  let rec lead_help (hi : int) (lo : int) : int =
    if hi = lo then hi else
    let mid = (hi + lo) / 2 in
    let hi_part = W.extract_exn ~hi ~lo:(mid + 1) w in
    if W.is_zero (W.lnot hi_part) then lead_help mid lo
    else lead_help hi (mid + 1)
  in
  assert(lo >= 0);
  assert(hi >= lo);
  (lead_help hi lo)  + 1



let compute_l_s_b lsb1 lsb2 b1 b2 : int = if lsb1 < lsb2 then
    let interval = W.extract_exn ~hi:(lsb2 - 1) ~lo:lsb1 b2 in
    let w, bit = factor_2s interval in
    if W.is_zero w then lsb2 else bit + lsb1
  else if lsb1 > lsb2 then
    let interval =  W.extract_exn ~hi:(lsb1 - 1) ~lo:lsb2 b1 in
    let w, bit = factor_2s interval in
    if W.is_zero w then lsb1 else bit + lsb2
  else lsb1  (* lsb1 = lsb2 *)



let compute_m_s_b msb1 msb2 b1 b2 : int = if msb1 > msb2 then
    let interval = W.extract_exn ~hi:msb1 ~lo:(msb2 + 1) b2 in
    Option.value_map ~default:msb2
      (lead_1_bit interval)
      ~f:(fun b -> b + msb2 + 1)
  else if msb1 < msb2 then
    let interval =  W.extract_exn ~hi:msb2 ~lo:(msb1 + 1) b1 in
    Option.value_map ~default:msb1
      (lead_1_bit interval)
      ~f:(fun b -> b + msb1 + 1)
  else msb1  (* msb1 = msb2 *)


let compute_range_sep msb msb1 msb2 b1 b2 : int = if msb1 > msb2
  then if msb = msb1 then lead_1_bit_run b2 ~hi:msb1 ~lo:(msb2 + 1) else msb + 1
  else if msb1 < msb2 then
    if msb = msb2 then lead_1_bit_run b1 ~hi:msb2 ~lo:(msb1 + 1) else msb + 1
    (* TODO: this last branch is a guess; it is not explained in the paper
       Figure out whether it is correct.
    *)
  else -1


(* This algorithm closely follows the one in "Circular Linear Progressions
   in SWEET". It converts a CLP into an AP (terminology from the paper)
   by using the least non-wrapping superset.
 *)
let logand (p1 : t) (p2 : t) : t =
  let sz = get_and_check_sizes p1 p2 in
  let bot = bottom sz in
  let cardn_two = W.of_int ~width:(sz + 1) 2 in
  (* We canonize the inputs so that their n1 and n2 are their
     true cardinalities and they are finite
  *)
  let cp1 = canonize p1 in
  let cp2 = canonize p2 in
  (* We ensure that the cardinality of the second CLP is at
     least the cardinality of the first to collapse the two cases where
     once CLP has cardinality 1 and the other has cardinality 2.
   *)
  let p1, p2 = if W.(<=) (cardinality cp1) (cardinality cp2)
    then (cp1, cp2) else (cp2, cp1) in
  let open Monads.Std.Monad.Option.Syntax in
  Option.value ~default:bot begin
    if W.is_zero p1.cardn || W.is_zero p2.cardn then !!bot
    else if W.is_one p1.cardn && W.is_one p2.cardn then
      !!(create (W.logand p1.base p2.base))
    else if W.is_one p1.cardn && W.(=) p2.cardn cardn_two then
      (* CLPs can represent any two-element set exactly, so
         we compute the two elements of the set and return them.
       *)
      finite_end p2 >>= fun e2 ->
      let base = W.logand p1.base p2.base in
      let newE = W.logand p1.base e2 in
      let step = W.sub newE base in
      let cardn = cardn_two in
      !!(create base ~step ~cardn)
    else
      min_elem p1 >>= fun min_elem_p1 ->
      max_elem p1 >>= fun max_elem_p1 ->
      min_elem p2 >>= fun min_elem_p2 ->
      max_elem p2 >>= fun max_elem_p2 ->
      let _, twos_in_s1 = factor_2s p1.step in
      let _, twos_in_s2 = factor_2s p2.step in
      let least_significant_bit_p1 = if W.is_one p1.cardn then sz
      (* since the CLP is canonized, if p1.cardn > 1 then p1.step <> 0 *)
        else twos_in_s1 in
      let least_significant_bit_p2 = if W.is_one p2.cardn then sz
      (* since the CLP is canonized, if p2.cardn > 1 then p2.step <> 0 *)
        else twos_in_s2 in
      (* There is no most significant bit iff the cardinality is 1 *)
      let most_significant_bit_p1 = Option.value ~default:(-1)
          (lead_1_bit (W.logxor min_elem_p1 max_elem_p1)) in
      let most_significant_bit_p2 = Option.value ~default:(-1)
          (lead_1_bit (W.logxor min_elem_p2 max_elem_p2)) in
      let l_s_b = compute_l_s_b
          least_significant_bit_p1
          least_significant_bit_p2
          min_elem_p1 min_elem_p2 in
      let m_s_b = compute_m_s_b
          most_significant_bit_p1
          most_significant_bit_p2
          min_elem_p1 min_elem_p2 in
      if l_s_b > m_s_b then
        (* The result is a singleton *)
        let base = W.logand min_elem_p1 min_elem_p2 in
        !!(create base)
      else
        let range_sep = compute_range_sep m_s_b
            most_significant_bit_p1
            most_significant_bit_p2
            min_elem_p1 min_elem_p2
        in
        let mask = if l_s_b >= range_sep then W.zero sz
              else let ones = W.ones (range_sep - l_s_b) in
                let sized_ones = W.extract_exn ~hi:(sz - 1) ones in
                Word.lshift sized_ones (W.of_int ~width:sz l_s_b) in
        let safe_lower_bound =
          W.logand min_elem_p1 min_elem_p2 |> W.logand (W.lnot mask) in
        let safe_upper_bound = W.logand max_elem_p1 max_elem_p2 |>
                               W.logor mask |>
                               W.min max_elem_p1 |>
                               W.min max_elem_p2 in
        let twos_step = W.lshift (W.of_int 1 ~width:sz)
            (W.of_int l_s_b ~width:sz) in
        let step = if most_significant_bit_p1 > most_significant_bit_p2 &&
                      m_s_b = most_significant_bit_p1 &&
                      range_sep = l_s_b then
            W.max p1.step twos_step
          else if most_significant_bit_p2 > most_significant_bit_p1 &&
                      m_s_b = most_significant_bit_p2 &&
                      range_sep = l_s_b then
            W.max p2.step twos_step
          else twos_step in
        let b1_and_b2 = W.logand min_elem_p1 min_elem_p2 in
        let frac = cdiv (W.sub safe_lower_bound b1_and_b2) step in
        let base = W.add b1_and_b2 (W.mul step frac) in
        (* TODO: use cardn_from_bounds *)
        let cardn = W.div (W.sub safe_upper_bound base) step |> succ_exact in
        !!(create base ~step ~cardn)
  end

let logor (p1 : t) (p2 : t) : t = lnot (logand (lnot p1) (lnot p2))

let logxor (p1 : t) (p2 : t) : t =
  let width = get_and_check_sizes p1 p2 in
  let two = create (W.of_int 2 ~width) in
  let approx1 = logor (logand p1 (lnot p2)) (logand (lnot p1) p2) in
  (* equality taken from Hacker's Delight *)
  let approx2 = sub (add p1 p2) (mul (logand p1 p2) two) in
  (* since both approximations are sound, their intersection is sound *)
  intersection approx1 approx2

(* Note: this operation accepts inputs of different sizes as per the BAP IR *)
let lshift (p1 : t) (p2 : t) : t =
  let sz1 = bitwidth p1 in
  let p2 = canonize p2 in
  let open Monads.Std.Monad.Option.Syntax in
  Option.value ~default:(bottom sz1) begin
    finite_end p1 >>= fun e1 ->
    min_elem p2 >>= fun min_p2 ->
    max_elem p2 >>= fun max_p2 ->
    if W.(>=) max_p2 (W.of_int sz1 ~width:(W.bitwidth max_p2)) then
      let msg = "During lshift, maximum element of CLP2 is >= CLP1's width" in
      !!(not_implemented ~top:(top sz1) msg)
    else
      let max_p2_int = W.to_int_exn max_p2 in
      let base = W.lshift p1.base min_p2 in
      let step = if is_one p2.cardn
        then W.lshift p1.step min_p2
        else W.lshift (bounded_gcd p1.base p1.step) min_p2 in
      let e_no_wrap = lshift_exact e1 max_p2_int in
      let e_width = W.bitwidth e_no_wrap in
      (* same as cardn_from_bounds, but adapted to e_no_wrap's bitwidth *)
      let cardn = if W.is_zero step then W.one 1 else
          let base_ext = W.extract_exn ~hi:(e_width - 1) base in
          let step_ext = W.extract_exn ~hi:(e_width - 1) step in
          let div_by_step = W.div (W.sub e_no_wrap base_ext) step_ext in
          (* extract adds an extra bit at the high end so that
             the call to succ never wraps to 0.
          *)
          W.succ (W.extract_exn ~hi:e_width div_by_step) in
      !!(create base ~step ~cardn)
  end

(* Note, this function only accepts CLPs that are the same bitwidth. *)
let rshift_step rshift ~p1 ~p2 ~e2 ~sz1 ~sz2 =
  assert(sz1 = sz2);
  let _, b1twos = factor_2s p1.base in
  let _, s1twos = factor_2s p1.step in
  let s1_divisible = W.(>=) (W.of_int s1twos ~width:sz1) e2 in
  let b1_divisible = W.(>=) (W.of_int b1twos ~width:sz1) e2 in
  let b1_initial_ones = count_initial_1s p1.base in
  if (s1_divisible && W.is_one p2.cardn) ||
     (s1_divisible && b1_divisible) ||
     (s1_divisible && W.(>=) (W.of_int ~width:sz2 b1_initial_ones) e2)
  then bounded_gcd (rshift p1.step e2) @@ W.sub (rshift p1.base @@ W.sub e2 p2.step)
      (rshift p1.base @@ e2)
  else W.one sz1

(* Note: [p1] and [p2] must have the same bitwidth, since this function
   depends on the [rshift_step] function above. *)
let rshift (p1 : t) (p2 : t) : t =
  let sz1 = bitwidth p1 in
  let sz2 = bitwidth p2 in
  let p1 = unwrap @@ canonize p1 in
  let p2 = unwrap @@ canonize p2 in
  let open Monads.Std.Monad.Option.Syntax in
  Option.value ~default:(bottom sz1) begin
    finite_end p1 >>= fun e1 ->
    finite_end p2 >>= fun e2 ->
    let base = W.rshift p1.base e2 in
    if W.is_one p1.cardn && W.is_one p2.cardn
    then !!(create base)
    else
      let step = rshift_step W.rshift ~p1 ~p2 ~e2 ~sz1 ~sz2 in
      let cardn = cardn_from_bounds base step (W.rshift e1 p2.base) in
      !!(create base ~step ~cardn)
  end

(* Note: [p1] and [p2] must have the same bitwidth, since this function
   depends on the [rshift_step] function above.

   Note also that the SWEET paper's algorithm for arshift is incorrect.
   To compute the new [n] (cardinality) on p. 26, it has this condition:

   - [if b1 >= c1[n1 - 1]]

   We have altered that condition to this:

   - [if 0 >= c1[n1 - 1]]

   *)
let arshift (p1 : t) (p2 : t) : t =
  let sz1 = bitwidth p1 in
  let sz2 = bitwidth p2 in
  let zero = W.zero sz1 in
  let p1 = unwrap_signed @@ canonize p1 in
  let p2 = unwrap @@ canonize p2 in
  let open Monads.Std.Monad.Option.Syntax in
  Option.value ~default:(bottom sz1) begin

    finite_end p1 >>= fun e1 ->
    finite_end p2 >>= fun e2 ->

    if W.is_one p1.cardn && W.is_one p2.cardn
    then
      let base = W.arshift (W.signed p1.base) p2.base in
      !!(create base ~width:sz1)
    else

      let base =
        if W.(>=) (W.signed p1.base) zero
        then W.arshift (W.signed p1.base) e2
        else W.arshift (W.signed p1.base) p2.base
        in

      let step = rshift_step W.arshift ~p1 ~p2 ~e2 ~sz1 ~sz2 in

      let new_end =
        if W.(>=) (W.signed e1) zero
        then W.arshift (W.signed e1) p2.base
        else W.arshift (W.signed e1) e2
        in
      let cardn = cardn_from_bounds base step new_end in

      !!(create base ~step ~cardn)

  end

(* helper function; splits a CLP into two segments: one that contains all
   points from the base up to n inclusive and another that contains the rest.
*)
let split_at_n (p : t) n : t * t =
  (* The CLP is canonized so that it can be treated as finite *)
  let p = canonize p in
  (* The first set extends to the highest point on the CLP up to e *)
  let cardn1 = min (cardn_from_bounds p.base p.step n) p.cardn in
  (* The second set contains all of the other elements *)
  let cardn2 = W.sub p.cardn cardn1 in
  let p2_base = nearest_inf_succ (W.succ n) p.base p.step in
  {base = p.base; step = p.step; cardn = cardn1},
  {base = p2_base; step = p.step; cardn = cardn2}

(* helper function; produces a result that contains exactly the
   elements of the input clp extended to the given width. Always
   returns disjoint CLPs.
   Expects that width >= bitwidth p.
   Note: in most cases, p2 will represent the empty set. If dealing with
   both CLPs is difficult or imprecise, this represents an opportunity
   for optimization.
*)
let extract_exact ~width:(width : int) (p : t) : t * t =
  let p_width = bitwidth p in
  assert (width >= p_width);
  (* The CLP is canonized so that infinite CLPs do not have to be treated
     specially.
  *)
  let lastn = W.ones p_width in
  let p1, p2 = split_at_n p lastn in
  create ~width p1.base ~step:p1.step ~cardn:p1.cardn,
  create ~width p2.base ~step:p2.step ~cardn:p2.cardn

let extract_lo ?(lo = 0) (p : t) : t =
  let p = canonize p in
  let width = bitwidth p in
  let res_width = width - lo in
  assert(lo < width);
  if lo = 0 then p else
    let default = bottom res_width in
    Option.value_map ~default (finite_end p) ~f:begin fun e ->
      let base = W.extract_exn ~lo p.base in
      let ext_lo w = W.extract_exn ~hi:(lo - 1) w in
      let base_mod_2lo = ext_lo p.base in
      let step_mod_2lo = ext_lo p.step in
      (* If no carry is ever triggered, the low bits can be ignored.
         The low bits increase monotonically until they carry over
         into the high bits, so it suffices to show that the sum of the
         low bits never carries. Note that this computation assumes that
         p.cardn > 0.
      *)
      let max_step_effect = add_exact base_mod_2lo @@
        mul_exact step_mod_2lo (W.pred p.cardn) in
      let carry_bound = dom_size ~width:(W.bitwidth max_step_effect) lo in
      if W.(<) max_step_effect carry_bound then
        create base ~step:(W.extract_exn ~lo p.step) ~cardn:p.cardn
      else
        let e = W.extract_exn ~lo e in
        let step = W.one res_width in
        let cardn = cardn_from_bounds base step e in
        create base ~step ~cardn
    end

let extract_hi ?(hi = None) ?(signed = false) (p : t) : t =
  let sz = bitwidth p in
  let hiv = Option.value ~default:(bitwidth p - 1) hi in
  if not signed && hiv + 1 >= sz then
    let res1, res2 = extract_exact ~width:(hiv + 1) p in
    union res1 res2
  else if not signed then
    create ~width:(hiv+1) p.base ~step:p.step ~cardn:p.cardn
  else
    (* TODO: signed case is old; check and update *)
    let ext =  W.extract_exn ~hi:hiv in
    let ext_signed w = W.extract_exn ~hi:hiv (W.signed w) in
    Option.value_map ~default:(bottom (hiv + 1)) (finite_end p) ~f:begin
      fun e ->
        (* TODO: in particular this infinite case should be checked *)
        if is_infinite p then infinite (ext p.base, ext p.step)
        else
          (* negmin is the number of the form 10*; the most negative
             number when interpreted as signed. When signed, its predecessor
             is the  most positive (signed) number.
          *)
          let negmin = W.lshift (W.one sz) (W.of_int ~width:sz (sz-1)) in
          let posmax = W.pred negmin in
          if elem negmin p && elem posmax p &&
             (p.base <> negmin || e <> posmax) then
            (* TODO: this case in highly nontrivial and will require
               a loss of precision.
            *)
            not_implemented ~top:(top (hiv + 1))
              "extract signed crossing max signed int"
          else
            let e' = W.sub e p.base in
            let newE' = ext e' in
            let base = if signed then ext_signed p.base else ext p.base in
            let step = ext p.step in
            (* If newE' wraps around, then it encompasses the full circle *)
            if W.(<) newE' e' then infinite(base, step)
            else
              let cardn = cardn_from_bounds (W.zero (hiv + 1)) step newE' in
              create base ~step ~cardn
    end

let extract_internal ?hi ?(lo = 0) ?(signed = false) (p : t) : t =
  let hi = Option.map hi ~f:(fun hi -> hi - lo) in
  extract_lo ~lo p |> extract_hi ~hi ~signed

let cast ct (sz : int) (p : t) : t = match ct with
  | Bil.UNSIGNED -> extract_internal ~hi:(sz - 1) p
  | Bil.SIGNED -> extract_internal ~hi:(sz - 1) ~signed:true p
  | Bil.LOW -> extract_internal ~hi:(sz - 1) p
  | Bil.HIGH -> extract_internal ~lo:(bitwidth p - sz) p

let extract ?hi:hi ?lo:lo (p : t) : t = extract_internal ?hi ?lo p

let concat (p1 : t) (p2 : t) : t =
  let width1 = bitwidth p1 in
  let width2 = bitwidth p2 in
  let width = width1 + width2 in
  let p1'base = lshift_exact p1.base width2 in
  let p1'step = lshift_exact p1.step width2 in
  let p1' = create p1'base ~step:p1'step ~cardn:p1.cardn in
  let p2' = cast Bil.UNSIGNED width p2 in
  (* TODO: bug in intersection? The following should work but does
     not on wrapping:
     (intersection (logor p1' p2') (add p1' p2'))
  *)
  (add p1' p2')

(* creates a CLP that soundly approximates the elements of the list *)
let of_list ~width l : t =
  assert (width > 0);
  let open Monads.Std.Monad.Option.Syntax in
  Option.value ~default:(bottom width) begin
    let l = List.map l ~f:(W.extract_exn ~hi:(width - 1) ~lo:0) in
    let l = List.sort ~compare:W.compare l in
    let diff_list = List.map2_exn l (rotate_list l) ~f:W.sub in
    let idx, _, step = List.foldi diff_list ~init:(0, W.zero width, W.zero width)
        ~f:(fun i (idx, diff, step) d ->
            assert(W.bitwidth diff = W.bitwidth step);
            assert(W.bitwidth diff = W.bitwidth d);
            if W.(>) d diff
             then i, d, bounded_gcd diff step
             else idx, diff, bounded_gcd d step) in
    let l = idx
            (* "rotate" the list left by the index of the desired first element *)
            |> List.split_n l
            |> (fun (end_l, start_l) -> List.append start_l end_l) in
    List.hd l >>= fun base ->
    List.last l >>= fun e ->
    let cardn = cardn_from_bounds base step e in
    assert(W.bitwidth base = width);
    !!{base; step; cardn}
  end

(* Note: BAP uses Z.div (standard division truncating
   towards 0 and obeying the rule of signs) internally
   for signed division and Z.ediv (the Euclidean algorithm)
   for unsigned division. This seems strange since Z.div and
   Z.ediv work the same way for nonnegative inputs. The
   implementations of div and sdiv here are consistent with
   both this approach and using just Z.div (since it would
   work the same way).
   TODO: Compute a more accurate step for the division.
*)
let div (p1 : t) (p2 : t) : t =
  let width = get_and_check_sizes p1 p2 in
  let open Monads.Std.Monad.Option.Syntax in
  Option.value ~default:(bottom width) begin
    min_elem p1 >>= fun min_e1 ->
    min_elem p2 >>= fun min_e2 ->
    max_elem p1 >>= fun max_e1 ->
    max_elem p2 >>= fun max_e2 ->
    if elem (W.zero width) p2 then not_implemented "Clp division by zero"
    else
      let base = W.div min_e1 max_e2 in
      let e = W.div max_e1 min_e2 in
      let step = if W.is_one (cardinality p2) &&
                    W.is_zero (W.modulo p1.step p2.base)
          then bounded_gcd (W.div p1.step p2.base)
              (W.sub (W.div p1.base p2.base) base)
              (* TODO: improve step precision in cases where
                 every element of the divisor divides every
                 element of the dividend
              *)
          else W.one width in
      let cardn = cardn_from_bounds base step e in
      !!{base; step; cardn}
  end

let sdiv (p1 : t) (p2 : t) : t =
  let wsdiv a b = W.div (W.signed a) (W.signed b) in
  let width = get_and_check_sizes p1 p2 in
  let open Monads.Std.Monad.Option.Syntax in
  Option.value ~default:(bottom width) begin
    min_elem p1 >>= fun min_e1 ->
    min_elem p2 >>= fun min_e2 ->
    max_elem p1 >>= fun max_e1 ->
    max_elem p2 >>= fun max_e2 ->
    if elem (W.zero width) p2 then not_implemented "Clp division by zero"
    else if W.is_one (cardinality p1) &&
            W.is_one (cardinality p2)
    then !!(singleton (wsdiv p1.base p2.base))
    else
      let minmax = wsdiv min_e1 max_e2 in
      let minmin = wsdiv min_e1 min_e2 in
      let maxmax = wsdiv max_e1 max_e2 in
      let maxmin = wsdiv max_e1 min_e2 in
      let base =
        min minmax @@
        min minmin @@
        min maxmax maxmin in
      let e =
        max minmax @@
        max minmin @@
        max maxmax maxmin in
      (* TODO: improve step accuracy *)
      let step = W.one width in
      let cardn = cardn_from_bounds base step e in
      !!{base; step; cardn}
  end

(* implemented as per the "SWEET" paper *)
let modulo (p1 : t) (p2 : t) : t =
  sub p1 (mul (div p1 p2) p2)

(* implemented as per the "SWEET" paper *)
let smodulo (p1 : t) (p2 : t) : t =
  sub p1 (mul (sdiv p1 p2) p2)

(* Implement indexed lattice *)
type idx = int
let get_idx = bitwidth
let precedes = subset
let join = union
let meet = intersection

(* TODO: There is still room for improvement on this *)
let widen_join (p1 : t) (p2 : t) =
  assert (subset p1 p2);
  if equal p1 p2 then p1 else
  infinite (p2.base, p2.step)

(* Implement the Value interface *)

(* NOTE: this compare function is solely for implementation of the value
   interface. It has the property that compare a b = 0 iff equal a b, but
   otherwise the ordering is arbitrary (though still properly transitive).
   Importantly, precedes a b DOES NOT imply compare a b <= 0 or vice versa.
*)
let compare (p1 : t) (p2 : t) : int =
  let p1 = canonize p1 in
  let p2 = canonize p2 in
  let base_comp = W.compare p1.base p2.base in
  let step_comp = W.compare p1.step p2.step in
  let cardn_comp = W.compare p1.cardn p2.cardn in
  let if_nzero_else a b = if a = 0 then b else a in
  if_nzero_else base_comp @@
  if_nzero_else step_comp @@
  cardn_comp


let sexp_of_t (p : t) : Sexp.t =
  let p = canonize p in
  Sexp.List begin match finite_end p with
    | Some e ->
      if W.is_one p.cardn then [W.sexp_of_t p.base]
      else if W.is_one @@ W.pred @@ p.cardn then
        [W.sexp_of_t p.base; W.sexp_of_t e]
      else [W.sexp_of_t p.base;
            W.sexp_of_t (W.add p.base p.step);
            Sexp.Atom "...";
            W.sexp_of_t e]
    | None -> [Sexp.Atom "{}"; Sexp.Atom (string_of_int (bitwidth p))]
  end

let t_of_sexp : Sexp.t -> t = function
  | Sexp.List [Sexp.Atom "{}"; Sexp.Atom s] ->
    let width = int_of_string s in
    bottom width
  | Sexp.List [be] ->
    let base = Word.t_of_sexp be in
    create base
  | Sexp.List [be; ne as ee]
  | Sexp.List [be; ne; Sexp.Atom "..."; ee] ->
    let base = Word.t_of_sexp be in
    let next = Word.t_of_sexp ne in
    let e = Word.t_of_sexp ee in
    let step = Word.sub next base in
    let cardn = cardn_from_bounds base step e in
    {base; step; cardn}
  | Sexp.List _
  | Sexp.Atom _ -> failwith "Sexp not a CLP"

(* Printing *)

let pp ppf (p : t) =
  let p = canonize p in
  let width = bitwidth p in
  match finite_end p with
  | None -> Format.fprintf ppf "{}:%i" width
  | Some _ when W.is_one p.cardn ->
    Format.fprintf ppf "@[{%a}:%i@]" W.pp p.base width
  | Some e when W.is_one @@ W.pred p.cardn ->
    Format.fprintf ppf "@[{%a,@ %a}:%i@]"
      W.pp p.base
      W.pp e
      width
  | Some e ->
    Format.fprintf ppf "@[{%a,@ %a,@ ...,@ %a}:%i@]"
      W.pp p.base
      W.pp (W.add p.base p.step)
      W.pp e
      width

let spp (p : t) : string = Format.asprintf "%a" pp p
