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

(**

   This module is used to compute and load intruction properties in order to
   handle instructions with unknown semantics. It exposes the slots that contain
   these properties.

*)

open Bap.Std
open Bap_core_theory

(** Slot containing the registers that are referenced in an assembly
    instruction. *)
val registers : (Theory.Semantics.cls, Var.Set.t) KB.slot
