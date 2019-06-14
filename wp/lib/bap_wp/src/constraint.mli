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

type z3_expr = Z3.Expr.expr

type t

type goal

val mk_goal : string -> z3_expr -> goal

val goal_to_string : goal -> string

val to_string : t -> string

val pp_constr : Format.formatter -> t -> unit

val mk_constr : goal -> t

val mk_ite : Bap.Std.Tid.t -> z3_expr -> t -> t -> t

val mk_clause : t list -> t list -> t

val eval : t -> Z3.context -> z3_expr

val substitute : t -> z3_expr list -> z3_expr list -> t

val substitute_one : t -> z3_expr -> z3_expr -> t
