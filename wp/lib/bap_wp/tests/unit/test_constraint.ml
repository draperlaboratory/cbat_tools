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

open !Core_kernel
open Bap.Std
open OUnit2
open Bap_wp
open Bil_to_bir
open Test_utils

module Pre = Precondition
module Constr = Constraint
module Bool = Z3.Boolean
module Expr = Z3.Expr
module BV = Z3.BitVector
module Array = Z3.Z3Array

(* To run these tests: `make test.unit` in bap_wp directory *)

let test_get_refuted_goals (test_ctx : test_ctxt) : unit =
  let ctx = Z3.mk_context [] in
  let solver = Z3.Solver.mk_simple_solver ctx in
  let x = BV.mk_const_s ctx "x" 32 in
  let one = BV.mk_numeral ctx "1" 32 in
  let two = BV.mk_numeral ctx "2" 32 in
  let exp_1 = Bool.mk_eq ctx x one
              |> Constr.mk_goal "x = 1"
              |> Constr.mk_constr
  in
  let exp_2 = Bool.mk_eq ctx x two
              |> Constr.mk_goal "x = 2"
              |> Constr.mk_constr
  in
  let clause = Constr.mk_clause [exp_1] [exp_2] in
  let result = Pre.check solver ctx clause in
  assert_equal ~ctxt:test_ctx ~printer:Z3.Solver.string_of_status
    Z3.Solver.SATISFIABLE result;
  let goals = Constr.get_refuted_goals clause solver ctx in
  Sequence.iter goals ~f:(fun g ->
      assert_equal ~ctxt:test_ctx ~printer:Expr.to_string ~cmp:Expr.equal
        (Bool.mk_eq ctx x two) (Constr.get_goal_val g.goal))

let test_get_refuted_goals_mem (test_ctx : test_ctxt) : unit =
  let ctx = Z3.mk_context [] in
  let solver = Z3.Solver.mk_simple_solver ctx in
  let sort = BV.mk_sort ctx 32 in
  let mem = Array.mk_const_s ctx "mem" sort sort in
  let addr = BV.mk_numeral ctx "11111111" 32 in
  let data1 = BV.mk_numeral ctx "22222222" 32 in
  let data2 = BV.mk_numeral ctx "33333333" 32 in
  let store1 = Array.mk_store ctx mem addr data1 in
  let store2 = Array.mk_store ctx mem addr data2 in
  let goal = Bool.mk_eq ctx store1 store2 in
  let constr = goal
               |> Constr.mk_goal (Expr.to_string goal)
               |> Constr.mk_constr
  in
  let result = Pre.check solver ctx constr in
  assert_equal ~ctxt:test_ctx ~printer:Z3.Solver.string_of_status
    Z3.Solver.SATISFIABLE result;
  let goals = Constr.get_refuted_goals constr solver ctx in
  Sequence.iter goals ~f:(fun g ->
      assert_equal ~ctxt:test_ctx ~printer:Expr.to_string ~cmp:Expr.equal
        goal (Constr.get_goal_val g.goal))

let test_substitute (test_ctx : test_ctxt) : unit =
  let ctx = Z3.mk_context [] in
  let x = BV.mk_const_s ctx "x" 32 in
  let one = BV.mk_numeral ctx "1" 32 in
  let exp = Bool.mk_eq ctx x one
            |> Constr.mk_goal "x = 1"
            |> Constr.mk_constr
  in
  let subst = Constr.substitute_one exp x one in
  let result = Constr.eval subst ctx in
  let expected = Bool.mk_eq ctx one one in
  assert_equal ~ctxt:test_ctx ~printer:Z3.Expr.to_string
    expected result

let test_substitute_order (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let solver = Z3.Solver.mk_simple_solver ctx in
  let var_gen = Env.mk_var_gen () in
  let env = Pre.mk_default_env ctx var_gen in
  let x = Var.create "x" reg32_t in
  let post_expr = Bool.mk_eq ctx (BV.mk_const_s ctx "x" 32) (BV.mk_numeral ctx "1" 32) in
  let sub = Bil.(
      [ x := i32 1;
        x := i32 2;
      ]
    ) |> bil_to_sub
  in
  let post = post_expr
             |> Constr.mk_goal "x = 1"
             |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_sub env post sub in
  let result = Pre.check solver ctx pre in
  assert_equal ~ctxt:test_ctx ~printer:Z3.Solver.string_of_status
    Z3.Solver.SATISFIABLE result;
  let goals = Constr.get_refuted_goals pre solver ctx in
  Sequence.iter goals ~f:(fun g ->
      assert_equal ~ctxt:test_ctx ~printer:Expr.to_string ~cmp:Expr.equal
        post_expr (Constr.get_goal_val g.goal))

let suite = [
  "Get Refuted Goals"             >:: test_get_refuted_goals;
  "Get Refuted Goals with Memory" >:: test_get_refuted_goals_mem;
  "Substitute Exprs"              >:: test_substitute;
  "Substitute Exprs in Order"     >:: test_substitute_order;
]
