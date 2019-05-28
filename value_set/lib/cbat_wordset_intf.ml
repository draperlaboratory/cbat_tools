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

module type S = sig
  type t [@@deriving bin_io, sexp]

  include Value.S with type t := t

  (* TODO: want to form a (pointed) semilattice w/ finset; take this out of intf? *)
  include Cbat_lattice_intf.S_indexed
    with type t := t and type idx = int

  (* TODO: what is/are the best constructor(s) to include? *)
  val of_list : width:int -> word list -> t
  val singleton : word -> t

  val bitwidth : t -> int

  val cardinality : t -> word

  val min_elem : t -> word option
  val max_elem : t -> word option

  val min_elem_signed : t -> word option
  val max_elem_signed : t -> word option
  
  val nearest_pred : word -> t ->  word option
  val nearest_succ : word -> t ->  word option

  (* Determines whether the set is spaced by a multiple of w
     when considered as an interval in the range [0..2^sz)
  *)
  val splits_by : t -> word -> bool

  val elem : word -> t -> bool
  val iter : t -> word list

  val equal : t -> t -> bool
  val overlap : t -> t -> bool

  (* TODO: these are aliases for lattice functions. Include or no? *)
  val union : t -> t -> t
  val intersection : t -> t -> t

  val add : t -> t -> t
  val sub : t -> t -> t
  val mul : t -> t -> t
  val div : t -> t -> t
  val sdiv : t -> t -> t
  val modulo : t -> t -> t
  val smodulo : t -> t -> t

  val arshift : t -> t -> t
  val rshift : t -> t -> t
  val lshift : t -> t -> t
  val logand : t -> t -> t
  val logor : t -> t -> t
  val logxor : t -> t -> t

  val lnot : t -> t
  val neg : t -> t

  val extract : ?hi:int -> ?lo:int -> t -> t
  val cast : Bil.cast -> int -> t -> t
  val concat : t -> t -> t

end

(* TODO: module Defaults *)
