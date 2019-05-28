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

open Core_kernel
open Bap.Std

(** Cbat_ai_memmap
    Represents memory as an interval tree from ranges of addresses
    to CLPs with an endianness. Note that, while BAP breaks up its
    memory into constant size (usually 8-bit) regions, this module
    does not. This is because n*k-bit CLPs cannot be well-represented
    as k n-bit CLPs. For example, take the set {0x17, 0x2e, 0x45}
    which can be represented exactly as a 3-element CLP with a
    constant step of 0x17. If we divide it into two 4-bit sets,
    we get {0x5, 0x7, 0xe} for the lower bits and {0x1, 0x2, 0x4}
    for the upper ones. However, this latter set cannot be represented
    by a CLP since it has a variable step. The closest approximation
    is {0x1, 0x2, 0x3, 0x4}. We then lose even more precision when
    attempting to read back an 8-bit word from these 4-bit cells.
    Since it is no longer clear which element from the low set
    corresponds to each element from the high set, the best a general
    algorithm can do is to guess the following set:
    {0x15, 0x17, 0x1e, 0x25, 0x27, 0x2e, 0x35, 0x37, 0x3e, 0x45, 0x47, 0x4e}
    Again, this set cannot be represented accurately by a CLP. The
    best we can do is the interval [0x15,0x4e] which has cardinality
    0x39 = 57, whereas our initial set had cardinality 3.  Since
    fixed-size memory cells handle larger data so badly, this module
    attempts to keep data stored at the greatest bitwidth possible.
*)

module WordSet = Cbat_clp_set_composite

module Key : sig

  type t

  val t_of_sexp : Sexp.t -> t
  val sexp_of_t : t -> Sexp.t

  val of_wordset : WordSet.t -> t option
end



module Val : sig

  type t

  module Idx : Cbat_lattice_intf.S_semi with type t = WordSet.idx * endian

  include Cbat_lattice_intf.S_indexed with type t := t and type idx = Idx.t

  val create : WordSet.t -> endian -> t

  val data : t -> WordSet.t

  val is_top : t -> bool
  val is_bottom : t -> bool

  val join_at : idx -> t -> t -> t
  val meet_at : idx -> t -> t -> t

  val join_poly : t -> t -> t
  val meet_poly : t -> t -> t

end



type t
type idx = {addr_width:int; addressable_width:int}

include Value.S with type t := t

include Cbat_map_lattice.S_indexed with module Val := Val and module Key := Key and
type t := t and type idx := idx
