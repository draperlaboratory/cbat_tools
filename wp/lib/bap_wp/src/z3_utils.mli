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
  Constr.z3_expr Bap.Std.Var.Map.t -> string -> (Bap.Std.Var.t -> string) -> (Constr.z3_expr option)

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

(** [construct_pointer_constraint] generates a constraint that
    the registers (passed in as z3 expressions) are treated as pointers. That is,
    all specified registers cannot point to the uninitalized stack region.
    They must be either below the bottom of the stack or above the initial
    stack pointer. *)
val construct_pointer_constraint : Constr.z3_expr list -> Env.t -> (Constr.z3_expr list) option -> Env.t option -> Constr.t

(** [mk_and] is a slightly optimized version of [Bool.mk_and] that does not produce an 
    [and] node if the number of operands is less than 2. This may improve sharing,
    but also improves compatibility of smtlib2 expressions with other solvers.  *)

val mk_and : Z3.context -> Constr.z3_expr list -> Constr.z3_expr

(** [check_external] invokes an external smt solver as a process. It communicates to the 
    process via a fairly rigid interpretation of the smtlib2 protocol. It extracts the 
    smtlib2 query string from the given z3_solver, queries the external solver, receives 
    a counter model if SAT. It then asserts this model back to the z3_solver, which should
    check quickly. This solver can then be used with the regular cbat z3 model 
    interpretation machinery. Tested with boolector, results with other solvers may vary.*)

val check_external : Z3.Solver.solver
  -> string
  -> Z3.context
  -> (Z3.FuncDecl.func_decl * Z3.Symbol.symbol) list
  -> Z3.Solver.status
