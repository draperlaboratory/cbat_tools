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

   This module exports types and utilities to process and report results found uisng the wp plugin.

*)

module Expr = Z3.Expr

module Arith = Z3.Arithmetic

module BV = Z3.BitVector

module Bool = Z3.Boolean

module Array = Z3.Z3Array

module Env = Environment

module Constr = Constraint

(** Prints out the result from check, and if the result is [SAT], generate a model that
    represents the registers and memory values that lead to a specific program state. *)
val print_result : Z3.Solver.solver -> Z3.Solver.status -> Constr.t
  -> orig:Env.t -> modif:Env.t -> unit


(** Prints to file a gdb script that will fill the appropriate registers with the countermodel *)
val output_gdb : Z3.Solver.solver -> Z3.Solver.status -> Env.t -> func:string -> filename:string -> unit

(** [mem_model] The default value stores the final else branch of a memory model. The model holds an association list of addresses and
    values held at those adresses. *)

type mem_model = {default : Constr.z3_expr ; model : (Constr.z3_expr * Constr.z3_expr) list}

(** [extract_array] takes a z3 expression that is a sequence of stores and converts it into
    a mem_model, which consists of a key/value association list and a default value *)

val extract_array : Constr.z3_expr -> mem_model