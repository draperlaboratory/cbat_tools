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

   This module implements the abstract data type of constraints which
   can be used as the input to the {!Precondition} module. These can
   then be used, e.g. to re-construct the counter-examples found by
   the verification process.

   For the most part, there are only 3 kinds of constraints:

   1. A constraint directly encoded by a Z3 expression, tagged by a
   name. Created with {!mk_goal}

   2. An if-then-else constraint. This constraint encodes a branch,
   along with the {!tid} of the branch location in BIL code, the
   branch condition, expressed as a Z3 expression, and the constraints
   along both branches. Created with {!mk_ite}.

   3. A clause constraint. Basically used for conjunctions of
   verification constraints and assumptions, of the form [A1 /\ ... /\
   An ==> V1 /\ ... /\ Vk] where the Ais and Vjs are assumptions and
   verification constraints, respectively.

*)

type z3_expr = Z3.Expr.expr

(** The base type of constraints. *)
type t

(** A goal is simply a Z3 (boolean) expression tagged with a name. *)
type goal

(** The branches that may be taken out of a conditional jump. *)
type branches = Only of bool | Both

(** A path tracks an execution path by mapping [jmp]s to [branches],
    where [branches] marks which branches were taken out of the [jmp]. *)
type path = branches Bap.Std.Jmp.Map.t

(** A goal that has been refuted by the Z3 model during WP analysis. Contains
    the path taken in the binary to reach the goal, as well as a map of register
    values at each jump in the path. *)
type refuted_goal

(** [mk_goal name e] creates a goal using a Z3 boolean expression and
    a name. *)
val mk_goal : string -> z3_expr -> goal

(** Creates a string representation of a goal. *)
val goal_to_string : ?colorful:bool -> goal -> string

(** Creates a string representation of a Z3 numeral as a hexadecimal in BAP notation. *)
val expr_to_hex : z3_expr -> string

(** Creates a string representation of a mapping of BAP variable names to their [z3_expr]s. *)
val format_values : Format.formatter -> (string * z3_expr) list -> unit

(** Creates a string representation of a goal that has been refuted given the model.
    This string shows the lhs and rhs of a goal that compares two values. If print_path
    is set, it also shows the path taken to reach the refuted goal and the register
    values along that path. *)
val format_refuted_goal
  :  refuted_goal
  -> Z3.Model.model
  -> orig:(z3_expr Bap.Std.Var.Map.t * Bap.Std.Sub.t)
  -> modif:(z3_expr Bap.Std.Var.Map.t * Bap.Std.Sub.t)
  -> print_path:bool
  -> string

(** Obtains the goal data type from a refuted goal. *)
val goal_of_refuted_goal : refuted_goal -> goal

(** Obtains the path data type from a refuted goal. *)
val path_of_refuted_goal : refuted_goal -> path

(** Obtains a goal's tagged name. *)
val get_goal_name : goal -> string

(** Obtains the [z3_expr] representing the value of the goal. *)
val get_goal_val : goal -> z3_expr

(** Creates a string representation of a constraint. *)
val to_string : ?colorful:(bool) -> t -> string

(** Pretty prints a constraint. *)
val pp : ?colorful:bool -> unit -> Format.formatter -> t -> unit

(** Creates a constraint made of a single goal. *)
val mk_constr : goal -> t

(** [mk_ite jmp e lc rc] creates an if-then-else constraint
    representing a branch at [jmp] with constraint [e], which has
    the constraints [lc] if [e] is true and [rc] otherwise. *)
val mk_ite : Bap.Std.Jmp.t -> z3_expr -> t -> t -> t

(** [mk_clause [a1;...,an] [v1;...;vm]] creates the constraint
    [a1 /\ ... /\ an ==> v1 /\ ... /\ vm]. *)
val mk_clause : t list -> t list -> t

(** [eval c ctx] evaluates the constraint [c] to a Z3 expression,
    using the standard Z3 encoding of if-then-else and clauses.
    If ~debug is called and is set to true, then statistics for
    eval will be printed. *)
val eval : ?debug:(bool) -> t -> Z3.context -> z3_expr

(** [substitute c [e1;...;e_n] [d1;...;d_n]] substitutes each
    occurence in [c] of the Z3 expression [ei] with the expression
    [di]. This is used extensively in the weakest precondition
    calculus. *)
val substitute : t -> z3_expr list -> z3_expr list -> t

(** [substitute_one c e d] is equivalent to [substitute c [e] [d]]. *)
val substitute_one : t -> z3_expr -> z3_expr -> t

(** [get_refuted_goals ~filter c solver ctx] obtains a list of goals that have
    been refuted by a Z3 model. The register map in the refuted goal will not
    save any z3 variable in [filter]. *)
val get_refuted_goals :
  ?filter_out:z3_expr list -> t -> Z3.Solver.solver -> Z3.context ->
  refuted_goal Bap.Std.Seq.t

(** Evaluates an expression in the current model. May raise an error if
    evaluation fails in the case that the argument contains quantifiers, is
    partial, or is not well-sorted. *)
val eval_model_exn : Z3.Model.model -> z3_expr -> z3_expr

(** Gets the model of the last check to the Z3 solver. An error will be raised
    if retrieving the model fails in the case that [check] was not yet called
    to the solver or the result of the last [check] did not result in SAT. *)
val get_model_exn : Z3.Solver.solver -> Z3.Model.model


(** stats, get_stats and print_stats are used for debugging purposes when
    the flag --wp-debug=constraint-stats is set. **)

(** Contains statistics for values of type t, keeping track of number of goals,
    ites, clauses and subs that compose t **)
type stats

(** [get_stats t stats] collects statistics of t, so that the statistics are
    held in stats **)
val get_stats : t -> stats -> unit

(** [print_stats t] calls get_stats to collect and print the statistics
    for the number of goals, ites, clauses and subs that compose t **)
val print_stats : t -> unit

(** [trivial ctx] generates a trivial constraint of [true]. *)
val trivial : Z3.context -> t
