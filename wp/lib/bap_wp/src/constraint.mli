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

(** A path tracks an execution path by mapping [tid]s of branches to a
    boolean, which marks whether the path was taken or not. *)
type path = bool Bap.Std.Tid.Map.t

(** [mk_goal name e] creates a goal using a Z3 boolean expression and
    a name. *)
val mk_goal : string -> z3_expr -> goal

(** Creates a string representation of a goal. *)
val goal_to_string : goal -> string

(** Creates a string representation of a goal that has been refuted given the model.
    This string shows the lhs and rhs of a goal that compares two values. *)
val refuted_goal_to_string : goal -> Z3.Model.model -> string

(** Obtains a goal's tagged name. *)
val get_goal_name : goal -> string

(** Obtains the [z3_expr] representing the value of the goal. *)
val get_goal_val : goal -> z3_expr

(** Creates a string representation of a constraint. *)
val to_string : t -> string

(** Pretty prints a constraint. *)
val pp_constr : Format.formatter -> t -> unit

(** Creates a constraint made of a single goal. *)
val mk_constr : goal -> t

(** [mk_ite tid e lc rc] creates an if-then-else constraint
    representing a branch at [tid] with constraint [e], which has
    the constraints [lc] if [e] is true and [rc] otherwise. *)
val mk_ite : Bap.Std.Tid.t -> z3_expr -> t -> t -> t

(** [mk_clause [a1;...,an] [v1;...;vm]] creates the constraint
    [a1 /\ ... /\ an ==> v1 /\ ... /\ vm]. *)
val mk_clause : t list -> t list -> t

(** [eval c ctx] evaluates the constraint [c] to a Z3 expression,
    using the standard Z3 encoding of if-then-else and clauses. *)
val eval : t -> Z3.context -> z3_expr

(** [substitute c [e1;...;e_n] [d1;...;d_n]] substitutes each
    occurence in [c] of the Z3 expression [ei] with the expression
    [di]. This is used extensively in the weakest precondition
    calculus. *)
val substitute : t -> z3_expr list -> z3_expr list -> t

(** [substitute_one c e d] is equivalent to [substitute c [e] [d]]. *)
val substitute_one : t -> z3_expr -> z3_expr -> t

(** Obtains a list of pairs of goals and a path to that goal that have
    been refuted by a Z3 model. *)
val get_refuted_goals_and_paths : t -> Z3.Model.model -> Z3.context
  -> (goal * path) Core_kernel.Sequence.t

(** Obtains a list of goals that have been refuted by a Z3 model. *)
val get_refuted_goals : t -> Z3.Model.model -> Z3.context -> goal Core_kernel.Sequence.t
