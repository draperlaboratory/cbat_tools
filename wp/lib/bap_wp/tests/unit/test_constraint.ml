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
open OUnit2
open Bap_wp

module Pre = Precondition
module Constr = Constraint
module Bool = Z3.Boolean
module Expr = Z3.Expr
module BV = Z3.BitVector

(* To run these tests: `make test.unit` in bap_wp directory *)

let test_get_violated_constr (test_ctx : test_ctxt) : unit =
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
  let goals = Constr.get_violated_goals clause model ctx in
  List.iter goals ~f:(fun g ->
      assert_equal ~ctxt:test_ctx ~printer:Expr.to_string ~cmp:Expr.equal
        (Bool.mk_eq ctx x two) (Constr.get_goal_val g))


let suite = [
  "Get Violated Constr" >:: test_get_violated_constr;
]
