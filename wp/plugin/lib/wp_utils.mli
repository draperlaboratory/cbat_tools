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

   This module contains various utility functions for the WP plugin. It contains
   functions for obtaining the program representation of a binary, updating
   default options in the WP analysis, and outputting results to the specified
   files.

*)

open Bap_main
open Bap.Std
open Bap_core_theory

(** The loader WP uses for lifting a binary, defaulting to LLVM. *)
val loader : string

(** Obtains the project binary at the given filepath using the BAP
   context and loader for lifting the binary. *)
val read_project :
  ctxt -> loader:string -> filepath:string -> Project.t
