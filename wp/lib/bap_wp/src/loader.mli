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
open Bap_core_theory

(** Slot containing the registers that are referenced in an assembly
    instruction. *)
val registers : (Theory.Semantics.cls, Var.Set.t) KB.slot

(** Slot that states whether an instruction is lifted as an intrinsic call or
    not. *)
val intrinsic : (Theory.Semantics.cls, bool option) KB.slot
