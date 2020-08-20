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

   This module contains the parameters the user can set from the command line
   interface to WP. These flags specify which properties WP should check
   and updates the default options.

*)

(** An exception that is raised when a user inputs an invalid options to a
    parameter or when the inputted parameters are not compatible to with each
    other. *)
exception Invalid_input

(** The available options to be set. Each flag corresponds to a parameter in
    the set with the BAP custom command line. *)
type t = {
  func : string;
  precond : string;
  postcond : string;
  trip_asserts : bool;
  check_null_derefs : bool;
  compare_func_calls : bool;
  compare_post_reg_values : string list;
  inline : string option;
  num_unroll : int option;
  gdb_output : string option;
  bildb_output : string option;
  use_fun_input_regs : bool;
  mem_offset : bool;
  debug : string list;
  stack_base : int option;
  stack_size : int option;
  show : string list
}

(** [validate flags files] ensures the user inputted the appropriate flags for
    the inputted [files]. In the case the user has invalid flags, an error
    message will print and WP will exit. *)
val validate : t -> string list -> unit

(** [validate_func name] checks the user inputted a [name] for the function to
    analyze. Raises {!Invalid_input} when [name] is empty. *)
val validate_func : string -> unit

(** [validate_debug options] checks the user inputted the supported options for
    the debug printer flag. Raises {!Invalid_input} when an unsupported option
    is inputted. *)
val validate_debug : string list -> unit

(** [validate_show options] checks the user inputted the supported options for
    the show printer flag. Raises {!Invalid_input} when an unsupported option
    is inputted. *)
val validate_show : string list -> unit

(** [validate_compare_func_calls flag files] checks that the flag is only set
    when there are two files to compare. Raises {!Invalid_input} otherwise. *)
val validate_compare_func_calls : bool -> string list -> unit

(** [validate_compare_post_reg_vals regs files] checks that the list of
    registers to compare is only set when there are two files to compare.
    Raises {!Invalid_input} otherwise. *)
val validate_compare_post_reg_vals : string list -> string list -> unit
