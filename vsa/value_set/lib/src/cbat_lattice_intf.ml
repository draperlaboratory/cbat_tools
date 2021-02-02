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

module type S_semi = sig
  type t

  val top : t
  val join : t -> t -> t

  (* Computes an approximation of the join of two lattices such that
     successive widening converges (reasonably quickly) to a fixpoint.
     This can be equivalent to join on lattices with small enough finite height.
  *)
  val widen_join : t -> t -> t

  (* Gives a partial order for the lattice. *)
  val precedes : t -> t -> bool
  (* Convenience function since equality can often be
     implemented more efficiently than precedes
  *)
  val equal : t -> t -> bool

end


module type S = sig

  include S_semi

  val bottom : t
  val meet : t -> t -> t

end

(* Represents a family of lattices indexed by another type.
   The lattice structure is maintained over elements with the
   same index. Meet, join, and precedes should be expected to error if
   passed elements with different indices.
*)
module type S_indexed = sig
  type t
  type idx

  val get_idx : t -> idx
  val top : idx -> t
  val bottom : idx -> t

  val meet : t -> t -> t
  val join : t -> t -> t

  val widen_join : t -> t -> t

  val precedes : t -> t -> bool
  val equal : t -> t -> bool

end

module type S_val = sig
  type t
  include S with type t := t
  include Value.S with type t := t
end

module type S_indexed_val = sig
  type t
  include S_indexed with type t := t
  include Value.S with type t := t
end

module Free_index (L : S) : S_indexed
  with type idx = unit and type t = L.t
= struct
  type t = L.t
  type idx = unit

  let get_idx _ = ()
  let top _ = L.top
  let bottom _ = L.bottom

  let meet = L.meet
  let join = L.join

  let widen_join = L.widen_join

  let precedes = L.precedes
  let equal = L.equal

end

module Free_index_val (L : S_val) : S_indexed_val
  with type idx = unit and type t = L.t
= struct
  type t = L.t [@@deriving bin_io, compare, sexp]
  type idx = unit

  let get_idx _ = ()
  let top _ = L.top
  let bottom _ = L.bottom

  let meet = L.meet
  let join = L.join

  let widen_join = L.widen_join

  let precedes = L.precedes
  let equal = L.equal

  let sexp_of_t = L.sexp_of_t

  let pp = L.pp

end

(* a simple 2-element  lattice with true as top and false as bottom *)
module BoolLattice : sig

  type t = bool [@@deriving bin_io, sexp, compare]
  include S_val with type t := t

end = struct

  type t = bool[@@deriving bin_io, sexp, compare]

  let top = true
  let bottom = false
  let meet a b = a && b
  let join a b = a || b
  let widen_join = join
  let equal a b = a = b
  let precedes a b = (not a) || b (* definition of classical implication *)

  let pp ppf (b : t) = Format.fprintf ppf (if b then "top" else "bottom")

end
