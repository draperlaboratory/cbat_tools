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

open Core_kernel
open Bap.Std

module WordSet = Cbat_clp_set_composite

type t

include Cbat_lattice_intf.S_val with type t := t

val add_word : t -> key:var -> data:WordSet.t -> t
val add_memory : t -> key:var -> data:Cbat_ai_memmap.t -> t

val find_word : WordSet.idx -> t -> var -> WordSet.t
val find_memory : Cbat_ai_memmap.idx -> t -> var -> Cbat_ai_memmap.t
