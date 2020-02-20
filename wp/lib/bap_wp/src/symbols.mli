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

   This module exports utility functions for working with the objdump command.
   It currently uses objdump to get the names of symbols in the .data and .bss
   sections of a binary and their addresses.

*)

module Constr = Constraint

(** [symbol] is a mapping of a name to its starting addresses. *)
type symbol = string * Constr.z3_expr

(** [get_symbols filename] creates a map of the names of symbols in the
    .data and .bss sections of a binary mapped to their addresses. *)
val get_symbols : Z3.context -> string -> symbol list

(** Given a list of symbols from the original and modified binaries,
    returns a function that maps the address of a memory read in the
    original binary to the address of the read in the modified binary. *)
val get_offsets :
  Z3.context -> symbol list -> symbol list -> Constr.z3_expr -> Constr.z3_expr
