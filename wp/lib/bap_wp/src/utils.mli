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

   This module contains various utility functions.

*)

open Bap.Std

module Option_let : sig

  (** Let binding for [Option.bind]. *)
  val (let*) : 'a option -> ('a -> 'b option) -> 'b option

  (** Let binding for [Option.map]. *)
  val (let+) : 'a option -> ('a -> 'b) -> 'b option

end

(** Convert a set of variables to a string for printing debug logs. *)
val varset_to_string : Var.Set.t -> string

(** Find a subroutine by name within a sequence. Raises Not_found_s if
    there is no such function. *)
val find_func_err : sub term seq -> string -> Sub.t

(** [get_mod_func_name [(in_re, out_re),...] name] Determines the
    name of a modified subroutine based on whether [name] matches one
    of the [in_re] regexps, returning the corresponding [Some out_re]
    for that regexp, and [None] if no [in_re] expressions match.

    e.g. [get_mod_func_name [("\\(.*\\)", "\\1_mod")]] "foo" will return
    [Some "foo_mod"].
*)
val get_mod_func_name : (string * string) list -> string -> string option

(** Find a sequence of subroutines to inline based on the regex from
    the user. Retunrs the empty sequence if given [None]. *)
val match_inline : string option -> sub term seq -> sub term seq

(** If [init_mem] is [true] ([true] by default) load the memory image
    of a binary based on the filepath. Re-raises any encountered
    (fatal) errors.
    Returns empty memory if [init_mem = false].
 *)
val init_mem : ?ogre:string option -> ?init_mem:bool -> Image.path -> value memmap

module Code_addrs : sig
  type t [@@deriving bin_io]

  (** The empty set. *)
  val empty : t

  (** [collect proj] returns the set of known code addresses in [proj]. *)
  val collect : project -> t

  (** [containts t addr] returns [true] if [addr] is a code address in [t]. *)
  val contains : t -> addr -> bool
end

(** [print_diagnostics show] checks if the 'diagnostics' flag is in [show]. *)
val print_diagnostics : string list -> bool
