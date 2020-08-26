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

   This module exports utility functions for working with Z3. Unfortunately, the module
   hierarchy necessitates thats some things that might naturally be placed in here have to
   put elsewhere, in particular any functionality required by [Constr] or [Env].

*)

module Env = Environment
module Constr = Constraint

(** Splits up an smtlib2 string into a list of tokens that can be parsed. *)
val tokenize : string -> string list

(** Builds up an smtlib2 string from a list of tokens. *)
val build_str : string list -> string

(** Looks up a Z3 variable's name in the map based off of the name in BIL notation.
    [fmt] is used to add prefixes and suffixes to a variable name. For example,
    init_RDI_orig. *)
val get_z3_name :
  Constr.z3_expr Bap.Std.Var.Map.t -> string -> (Bap.Std.Var.t -> string) -> (Z3.Expr.expr option)

(** [get_decls_and_symbols] builds from a the var_map in an environment
    a mapping of all Z3 func_decl to their symbol. This is a helper function for
    [mk_smtlib2] *)
val get_decls_and_symbols : Env.t -> ((Z3.FuncDecl.func_decl * Z3.Symbol.symbol) list)

(** [mk_smtlib2_single env smtlib_str] takes in a string representing a
    valid SMT-Lib-2 statement.
    The variables in the SMT-Lib statements need to appear in the
    environment. The intended purpose of this function is generating hypothesis
     and postconditions for single binary analysis *)
val mk_smtlib2_single : Env.t -> string -> Constr.t

(** [mk_smtlib2] parses a smtlib2 string in the context that has a mapping of func_decl
    to symbols and returns a constraint [Constr.t] corresponding to the smtlib2 string.
    The [func_decl * symbol] mapping can be constructed from an [Env.t] using the
    [get_decls_and_symbols] function. *)
val mk_smtlib2 : Z3.context -> string -> ((Z3.FuncDecl.func_decl * Z3.Symbol.symbol) list)  -> Constr.t

(** [construct_pointer_constraint] generates a precondition that asserts that
    the register names provided in `l` are treated as pointers. That means
    all of these registers cannot point to the uninitalized stack region. This
    means, they must be either below the bottom of the stack or above the initial
    stack pointer. *)
val construct_pointer_constraint : string list -> int -> Z3.context -> Env.t -> Env.t option -> string
