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
open Bap_wp

module Env = Environment

(** The default loader WP uses for lifting a binary. The default loader is
    LLVM. *)
val loader : string

(** Obtains the program representation of the binary at the filepath using
    the BAP context and loader for lifting the binary. *)
val read_program : ctxt -> loader:string -> filepath:string -> Program.t

(** [find_func_err subs name] obtains a function named [name] from a
    sequence of subroutines [subs]. Fails if the function can't be found. *)
val find_func_err : Sub.t Seq.t -> string -> Sub.t

(** [match_inline regex subs] finds a sequence of subroutines to inline from
    [subs] that match with [regex]. *)
val match_inline : string option -> Sub.t Seq.t -> Sub.t Seq.t

(** Converts a set of variables to a string for printing debug logs. *)
val varset_to_string : Var.Set.t -> string

(** Updates the number of times to unroll a loop based on the user's input. *)
val update_default_num_unroll : int option -> unit

(** Returns a record that can be used when creating an {!Environment.t} to
    change the default the stacks base and size. *)
val update_stack : base:int option -> size:int option -> Env.mem_range

(** Checks if the user provided a filename to output a gdb script to. If a
    filename is provided, outputs the gdb script. *)
val output_to_gdb :
     filename:string option
  -> func:string
  -> Z3.Solver.solver
  -> Z3.Solver.status
  -> Env.t
  -> unit

(** Checks if the user provided a filename to input a bildb init file to. If a
    filename is provided, outputs the bildb init file. *)
val output_to_bildb :
     filename:string option
  -> Z3.Solver.solver
  -> Z3.Solver.status
  -> Env.t
  -> unit
