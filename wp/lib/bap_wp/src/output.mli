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

(** Prints out the result from check, and if the result is [SAT], generate a model that
    represents the registers and memory values that lead to a specific program state,
    a list of goals that have been refuted, and if specified, the paths that lead to
    the refuted goals. *)
val print_result
  : ?fmt:Format.formatter
  -> ?dump_cfgs:(string option)
  -> Z3.Solver.solver
  -> Z3.Solver.status
  -> Constr.t
  -> show:string list
  -> orig:(Bap.Std.sub Compare.code)
  -> modif:(Bap.Std.sub Compare.code)
  -> unit

(** Prints to file a gdb script that will fill the appropriate registers with the countermodel *)
val output_gdb :
  Z3.Solver.solver -> Z3.Solver.status -> Env.t -> func:string -> filename:string -> unit

(** [output_bildb solver status env file] prints to a YAML file that will fill
    the appropriate registers with the values found in the countermodel in the
    case the analysis returns SAT. This is used to initialize the BilDB plugin.*)
val output_bildb :
  Z3.Solver.solver -> Z3.Solver.status -> Env.t -> string -> unit

(** [mem_model] The default value stores the final else branch of a memory model. The model holds an association list of addresses and
    values held at those adresses. *)
type mem_model = {default : Constr.z3_expr ; model : (Constr.z3_expr * Constr.z3_expr) list}

(** [extract_array] takes a z3 expression that is a sequence of stores and converts it into
    a mem_model, which consists of a key/value association list and a default value *)
val extract_array : Constr.z3_expr -> mem_model
