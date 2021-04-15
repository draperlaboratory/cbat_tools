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

module Pre = Precondition
module Constr = Constraint
module Env = Environment
module Bool = Z3.Boolean
module BV = Z3.BitVector

(* To run these tests: `make test.unit` in bap_wp directory *)

let test_tgt = Test_utils.test_tgt

let test_mk_smtlib2_single_1 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env = Pre.mk_env ~target:test_tgt ctx var_gen in
  let x = Var.create "x" reg32_t in
  let y = Var.create "y" reg32_t in
  let z3_x, env = Env.get_var env x in
  let z3_y, env = Env.get_var env y in
  let init_x, env = Env.mk_init_var env x in
  let init_y, env = Env.mk_init_var env y in
  let cond = "(assert (and (= x init_x) (= y init_y)))" in
  let expected =
    let constr =
      Bool.mk_and ctx [Bool.mk_eq ctx z3_x init_x; Bool.mk_eq ctx z3_y init_y]
      |> Constr.mk_goal "(and (= x0 init_x0) (= y0 init_y0))"
      |> Constr.mk_constr
    in
    Constr.mk_clause [] [constr]
  in
  let result = Z3_utils.mk_smtlib2_single env cond in
  assert_equal ~ctxt:test_ctx
    ~printer:Constr.to_string
    expected result

let test_mk_smtlib2_single_2 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env = Pre.mk_env ~target:test_tgt ctx var_gen in
  let x = Var.create "x" reg32_t in
  let x123 = BV.mk_const_s ctx "x123" 32 in
  let z3_x, env = Env.get_var env x in
  let init_x, env = Env.mk_init_var env x in
  let cond =
    "(declare-const x123 (_ BitVec 32)) \n\
     (assert (and (= x init_x) (= x123 x)))"
  in
  let expected =
    let constr =
      Bool.mk_and ctx [Bool.mk_eq ctx z3_x init_x; Bool.mk_eq ctx x123 z3_x]
      |> Constr.mk_goal "(and (= x0 init_x0) (= x123 x0))"
      |> Constr.mk_constr
    in
    Constr.mk_clause [] [constr]
  in
  let result = Z3_utils.mk_smtlib2_single env cond in
  assert_equal ~ctxt:test_ctx
    ~printer:Constr.to_string
    expected result

let suite = [
  "Parsing smtlib single expression" >:: test_mk_smtlib2_single_1;
  "Should not overwrite x123"        >:: test_mk_smtlib2_single_2;
]
