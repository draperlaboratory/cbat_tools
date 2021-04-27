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


(** Update the number of times to unroll a loop based on the user's
   input. *)
val update_default_num_unroll : int option -> unit

(** Convert a set of variables to a string for printing debug logs. *)
val varset_to_string : Var.Set.t -> string

(** Find a subroutine by name within a sequence. Raises Not_found_s if
   there is no such function. *)
val find_func_err : sub term seq -> string -> Sub.t

(** [get_mod_func_name name [(in_re, out_re),...]] Determines the
   name of a modified subroutine based on whether [name] matches one
   of the [in_re] regexps, returning the corresponding [Some out_re]
   for that regexp, and [None] if no [in_re] expressions match.

    e.g. [get_mod_func_name "foo" [(".*", "\1_mod")]] will return
   [Some "foo_mod"].
*)
val get_mod_func_name : (string * string) list -> string -> string option

(** Find a sequence of subroutines to inline based on the regex from
    the user. Retunrs the empty sequence if given [None]. *)
val match_inline : string option -> sub term seq -> sub term seq

