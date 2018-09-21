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

open Bap.Std

(**
   This module implements Circular Linear Progressions in the style of
   [1] "Executable Analysis using Abstract Interpretation with Circular
   Linear Progressions"
   (http://www.csa.iisc.ernet.in/~cplse/papers/srikant-memocode-2007.pdf).
   The poset of CLPs is a superset of the poset of strided intervals that
   more precicely handles overflow and underflow.
*)

type t [@@deriving bin_io, sexp]

include Cbat_wordset_intf.S with type t := t

val create : ?width:int -> ?step:word -> ?cardn: word -> word -> t

val nearest_pred : word -> t -> word option
val nearest_succ : word -> t -> word option

val is_top : t -> bool
val is_bottom : t -> bool

val subset : t -> t -> bool

val spp : t -> string



