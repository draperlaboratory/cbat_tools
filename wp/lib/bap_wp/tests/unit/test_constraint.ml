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
open Test_utils

module Pre = Precondition
module Constr = Constraint
module Bool = Z3.Boolean
module Expr = Z3.Expr
module BV = Z3.BitVector

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
  let model = Z3.Solver.get_model solver
              |> Option.value_exn ?here:None ?error:None ?message:None in
  let goals = Constr.get_refuted_goals clause model ctx in
  Sequence.iter goals ~f:(fun g ->
      assert_equal ~ctxt:test_ctx ~printer:Expr.to_string ~cmp:Expr.equal
        (Bool.mk_eq ctx x two) (Constr.get_goal_val g))

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

(* let test_substitute_order (test_ctx : test_ctxt) : unit = *)
(*   let ctx = Env.mk_ctx () in *)
(*   let var_gen = Env.mk_var_gen () in *)
(*   let env = Pre.mk_default_env ctx var_gen in *)
(*   let x = Var.create "x" reg32_t in *)
(*   let y = Var.create "y" reg32_t in *)
(*   let z = Var.create "z" reg32_t in *)
(*  *)
(*   let block = Bil.( *)
(*       [ if_ ((var x) < (i32 10)) *)
(*           [y := (var x) + (i32 1)] *)
(*           [y := (var x) - (i32 1)]; *)
(*         z := var y *)
(*       ] *)
(*     ) |> bil_to_sub *)
(*   in *)
(*  *)
(*   let diff = mk_z3_expr env Bil.((var z) - (var x)) in *)
(*   let high  = BV.mk_sle ctx diff (BV.mk_numeral ctx "1" 32) in *)
(*   let low = BV.mk_sle ctx (BV.mk_numeral ctx "-1" 32) diff in *)
(*   let post = Bool.mk_and ctx [low; high] *)
(*              |> Constr.mk_goal "-1 <= z - x && z - x <= 1" *)
(*              |> Constr.mk_constr *)
(*   in *)
(*   let pre, _ = Pre.visit_sub env post sub in *)
(*   assert_z3_result test_ctx ctx (Sub.to_string sub) post pre Z3.Solver.UNSATISFIABLE *)

let suite = [
  "Get Refuted Goals" >:: test_get_refuted_goals;
  "Substitute Exprs"  >:: test_substitute;
]
