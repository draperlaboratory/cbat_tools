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

open Bap_main
open Bap_core_theory
open Bap.Std
open Monads.Std

module Env = Environment

(** A result monad that includes Extension.Error.t as the error type. This
    error is returned when a user passes in an invalid parameter. *)
module Err : Monad.Result.S with
  type 'a t := 'a Monad.Result.T1(Extension.Error)(Monad.Ident).t and
type 'a m := 'a Monad.Result.T1(Extension.Error)(Monad.Ident).m and
type 'a e := 'a Monad.Result.T1(Extension.Error)(Monad.Ident).e and
type err := Extension.Error.t

(** The available options to be set. Each flag corresponds to a parameter in
    the set with the BAP custom command line. *)
type t = {
  func : string;
  precond : string;
  postcond : string;
  trip_asserts : bool;
  check_null_derefs : bool;
  check_invalid_derefs : bool;
  compare_func_calls : bool;
  compare_post_reg_values : string list;
  pointer_reg_list : string list;
  inline : string option;
  num_unroll : int option;
  loop_invariant : string;
  gdb_output : string option;
  bildb_output : string option;
  use_fun_input_regs : bool;
  mem_offset : bool;
  rewrite_addresses : bool;
  debug : string list;
  stack_base : int option;
  stack_size : int option;
  show : string list;
  func_name_map : (string * string) list;
  user_func_specs : (string * string * string) list;
  user_func_specs_orig : (string * string * string) list;
  user_func_specs_mod : (string * string * string) list;
  fun_specs : string list;
  ext_solver_path : string option;
  init_mem : bool;
}

(** [validate flags files] ensures the user inputted the appropriate flags for
    the inputted [files]. In the case the user has invalid flags, an error is
    returned. *)
val validate : t -> string list -> (unit, error) result

(** [validate_func name] checks the user inputted a [name] for the function to
    analyze. Returns an error when [name] is empty. *)
val validate_func : string -> (unit, error) result

(** [validate_debug options] checks the user inputted the supported options for
    the debug printer flag. Returns an error when an unsupported option is
    inputted. *)
val validate_debug : string list -> (unit, error) result

(** [validate_show options] checks the user inputted the supported options for
    the show printer flag. Returns an error when an unsupported option is
    inputted. *)
val validate_show : string list -> (unit, error) result

(** [validate_compare_func_calls flag files] checks that the flag is only set
    when there are two files to compare. Returns an error otherwise. *)
val validate_compare_func_calls : bool -> string list -> (unit, error) result

(** [validate_compare_post_reg_vals regs files] checks that the list of
    registers to compare is only set when there are two files to compare.
    Returns an error otherwise. *)
val validate_compare_post_reg_vals :
  string list -> string list -> (unit, error) result

(** [validate_mem_flags flags files] checks that a memory comparison flag is
    only set when there are two files to compare, and that only one flag is set
    at a time. Returns an error otherwise. *)
val validate_mem_flags : t -> string list -> (unit, error) result

(** [validate_check_invalid_derefs flag files] checks that the flag is only set
    when there are two files to compare. Returns an error otherwise. *)
val validate_check_invalid_derefs : bool -> string list -> (unit, error) result

(** [parse_loop_environment invariant target sub] parses the [invariant] which
     is an S-expression representing the address of a loop header and its
     corresponding loop invariant, and returns a format accepted by the
     environment.

     i.e., [parse_loop_environment "(((address 0x12) (invariant
     "(assert (= foo bar))")))" x86 sub]. *)
val parse_loop_invariant :
  string -> Theory.target -> Sub.t -> Env.loop_invariants

(** Creates the default parameters for easy invocation *)
val default : func:string -> t
