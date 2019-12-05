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

   This module exports types and utilities to process and report results found
   using the WP plugin.

   The report contains information about the result of the WP analysis, and in
   the case the result is [SAT], prints out the model that contains the input
   register and memory values that result in the program refuting a goal, the path
   taken to the refuted goal, and the register values at each jump in the path.

*)

module Env = Environment
module Constr = Constraint


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