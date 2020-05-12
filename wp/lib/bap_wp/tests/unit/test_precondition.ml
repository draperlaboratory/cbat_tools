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
module Env = Environment
module Bool = Z3.Boolean
module Expr = Z3.Expr
module BV = Z3.BitVector


(* To run these tests: `make test.unit` in bap_wp directory *)

let assert_z3_result (test_ctx : test_ctxt) (env : Env.t) (body : string)
    (post : Constr.t) (pre : Constr.t) (expected : Z3.Solver.status) : unit =
  let z3_ctx = Env.get_context env in
  let solver = Z3.Solver.mk_simple_solver z3_ctx in
  let result = Pre.check solver z3_ctx pre in
  assert_equal ~ctxt:test_ctx
    ~printer:Z3.Solver.string_of_status
    ~pp_diff:(fun ff (exp, real) ->
        Format.fprintf ff "\n\nPost:\n%a\n\nAnalyzing:\n%sPre:\n%a\n\n%!"
          Constr.pp_constr post body Constr.pp_constr pre;
        print_z3_model solver exp real pre ~orig:env ~modif:env)
    expected result


let test_empty_block (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env = Pre.mk_env ctx var_gen  in
  let block = Blk.create () in
  let post = true_constr ctx in
  let pre, _ = Pre.visit_block env post block in
  assert_z3_result test_ctx env (Blk.to_string block) post pre Z3.Solver.UNSATISFIABLE


let test_assign_1 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen ()in
  let env = Pre.mk_env ctx var_gen  in
  let y = Var.create "y" reg32_t in
  let x = Var.create "x" reg32_t in
  let e = Bil.binop Bil.plus (Bil.var x) one in
  let block = Blk.create () |> mk_def y e in
  let post = Bool.mk_eq ctx (mk_z3_var env y) (mk_z3_expr env e)
             |> Constr.mk_goal "y = x + 1"
             |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_block env post block in
  assert_z3_result test_ctx env (Blk.to_string block) post pre Z3.Solver.UNSATISFIABLE


let test_assign_2 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env = Pre.mk_env ctx var_gen  in
  let y = Var.create "y" reg32_t in
  let x = Var.create "x" reg32_t in
  let e = Bil.binop Bil.plus (Bil.var x) one in
  let block = Blk.create () |> mk_def y e in
  let post = Bool.mk_eq ctx (mk_z3_var env y) (mk_z3_var env x)
             |> Constr.mk_goal "y = x"
             |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_block env post block in
  assert_z3_result test_ctx env (Blk.to_string block) post pre Z3.Solver.SATISFIABLE


let test_assign_3 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env = Pre.mk_env ctx var_gen  in
  let y = Var.create "y" reg32_t in
  let x = Var.create "x" reg32_t in
  let e = Bil.binop Bil.plus (Bil.var x) one in
  let e' = Bil.binop Bil.minus (Bil.var x) one in
  let block = Blk.create ()
              |> mk_def y (Bil.var x)
              |> mk_def x e
  in
  let post = Bool.mk_eq ctx (mk_z3_var env y) (mk_z3_expr env e')
             |> Constr.mk_goal "y = x - 1"
             |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_block env post block in
  assert_z3_result test_ctx env (Blk.to_string block) post pre Z3.Solver.UNSATISFIABLE


let test_phi_1 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env = Pre.mk_env ctx var_gen  in
  let l1_tid = Tid.create () in
  Tid.set_name l1_tid "test_l1";
  let l2_tid = Tid.create () in
  Tid.set_name l2_tid "test_l2";
  let x = Var.create "x" reg32_t in
  let x1 = Var.create "x1" reg32_t in
  let x2 = Var.create "x2" reg32_t in
  let phi_x = Phi.of_list x [(l1_tid, Bil.var x1); (l2_tid, Bil.var x2)] in
  let block = Blk.create () |> mk_phi phi_x in
  let x1_exp = Bool.mk_eq ctx (mk_z3_var env x) (mk_z3_var env x1) in
  let x2_exp = Bool.mk_eq ctx (mk_z3_var env x) (mk_z3_var env x2) in
  let post = Bool.mk_or ctx [x1_exp; x2_exp]
             |> Constr.mk_goal "x = x1 || x = x2"
             |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_block env post block in
  assert_z3_result test_ctx env (Blk.to_string block) post pre Z3.Solver.UNSATISFIABLE


let test_read_write_1 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env = Pre.mk_env ctx var_gen  in
  let x = Var.create "x" reg32_t in
  let y = Var.create "y" reg32_t in
  let addr = Var.create "addr" reg32_t in
  let mem = Var.create "mem" (Type.mem `r32 `r8) in
  let store = Bil.store ~mem:(Bil.var mem) ~addr:(Bil.var addr) (Bil.var x) LittleEndian `r32 in
  let load = Bil.load ~mem:(Bil.var mem) ~addr:(Bil.var addr) LittleEndian `r32 in
  let block = Blk.create ()
              |> mk_def mem store
              |> mk_def y load
  in
  let post = Bool.mk_eq ctx (mk_z3_var env y) (mk_z3_var env x)
             |> Constr.mk_goal "y = x"
             |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_block env post block in
  assert_z3_result test_ctx env (Blk.to_string block) post pre Z3.Solver.UNSATISFIABLE


let test_read_write_2 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env = Pre.mk_env ctx var_gen  in
  let x = Var.create "x" reg32_t in
  let y = Var.create "y" reg32_t in
  let addr = Var.create "addr" reg32_t in
  let mem = Var.create "mem" (Type.mem `r32 `r8) in
  let store = Bil.store ~mem:(Bil.var mem) ~addr:(Bil.var addr) (Bil.var x) BigEndian `r32 in
  let load = Bil.load ~mem:(Bil.var mem) ~addr:(Bil.var addr) BigEndian `r32 in
  let block = Blk.create ()
              |> mk_def mem store
              |> mk_def y load
  in
  let post = Bool.mk_eq ctx (mk_z3_var env y) (mk_z3_var env x)
             |> Constr.mk_goal "y = x"
             |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_block env post block in
  assert_z3_result test_ctx env (Blk.to_string block) post pre Z3.Solver.UNSATISFIABLE


let test_read_write_3 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env = Pre.mk_env ctx var_gen  in
  let x = Var.create "x" reg32_t in
  let y = Var.create "y" reg32_t in
  let addr = Var.create "addr" reg32_t in
  let mem = Var.create "mem" (Type.mem `r32 `r8) in
  let store = Bil.store ~mem:(Bil.var mem) ~addr:(Bil.var addr) (Bil.var x) BigEndian `r32 in
  let load = Bil.load ~mem:(Bil.var mem) ~addr:(Bil.var addr) LittleEndian `r32 in
  let block = Blk.create ()
              |> mk_def mem store
              |> mk_def y load
  in
  let post = Bool.mk_eq ctx (mk_z3_var env y) (mk_z3_var env x)
             |> Constr.mk_goal "y = x"
             |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_block env post block in
  assert_z3_result test_ctx env (Blk.to_string block) post pre Z3.Solver.SATISFIABLE


let test_read_write_4 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env = Pre.mk_env ctx var_gen  in
  let x = Var.create "x" reg32_t in
  let y = Var.create "y" reg32_t in
  let addr = Var.create "addr" reg32_t in
  let mem = Var.create "mem" (Type.mem `r32 `r8) in
  let store = Bil.store ~mem:(Bil.var mem) ~addr:(Bil.var addr) (Bil.var x) LittleEndian `r32 in
  let load = Bil.load ~mem:(Bil.var mem) ~addr:(Bil.var addr) BigEndian `r32 in
  let block = Blk.create ()
              |> mk_def mem store
              |> mk_def y load
  in
  let post = Bool.mk_eq ctx (mk_z3_var env y) (mk_z3_var env x)
             |> Constr.mk_goal "y = x"
             |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_block env post block in
  assert_z3_result test_ctx env (Blk.to_string block) post pre Z3.Solver.SATISFIABLE


let test_bit_shift_1 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env = Pre.mk_env ctx var_gen  in
  let x = Var.create "x" reg32_t in
  let y = Var.create "y" reg32_t in
  let lshift = Bil.binop Bil.lshift (Bil.var x) two in
  let rshift = Bil.binop Bil.rshift (lshift) two in
  let block = Blk.create ()
              |> mk_def x (Bil.int @@ Word.of_int 0x3fffffff ~width:32)
              |> mk_def y (Bil.var x)
              |> mk_def y lshift
              |> mk_def y rshift
  in
  let post = Bool.mk_eq ctx (mk_z3_var env y) (mk_z3_var env x)
             |> Constr.mk_goal "y = x"
             |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_block env post block in
  assert_z3_result test_ctx env (Blk.to_string block) post pre Z3.Solver.UNSATISFIABLE


let test_bit_shift_2 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env = Pre.mk_env ctx var_gen  in
  let x = Var.create "x" reg32_t in
  let y = Var.create "y" reg32_t in
  let lshift = Bil.binop Bil.lshift (Bil.var y) two in
  let rshift = Bil.binop Bil.rshift (Bil.var y) two in
  let block = Blk.create ()
              |> mk_def x (Bil.int @@ Word.of_int 0x40000000 ~width:32)
              |> mk_def y (Bil.var x)
              |> mk_def y lshift
              |> mk_def y rshift
  in
  let post = Bool.mk_eq ctx (mk_z3_var env y) (mk_z3_var env x)
             |> Constr.mk_goal "y = x"
             |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_block env post block in
  assert_z3_result test_ctx env (Blk.to_string block) post pre Z3.Solver.SATISFIABLE


let test_bit_ashift_1 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env = Pre.mk_env ctx var_gen  in
  let x = Var.create "x" reg32_t in
  let y = Var.create "y" reg32_t in
  let lshift = Bil.binop Bil.lshift (Bil.var x) two in
  let rshift = Bil.binop Bil.arshift (lshift) two in
  let block = Blk.create ()
              |> mk_def x (Bil.int @@ Word.of_int 0x1fffffff ~width:32)
              |> mk_def y (Bil.var x)
              |> mk_def y lshift
              |> mk_def y rshift
  in
  let post = Bool.mk_eq ctx (mk_z3_var env y) (mk_z3_var env x)
             |> Constr.mk_goal "y = x"
             |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_block env post block in
  assert_z3_result test_ctx env (Blk.to_string block) post pre Z3.Solver.UNSATISFIABLE


let test_bit_ashift_2 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env = Pre.mk_env ctx var_gen  in
  let x = Var.create "x" reg32_t in
  let y = Var.create "y" reg32_t in
  let lshift = Bil.binop Bil.lshift (Bil.var y) two in
  let rshift = Bil.binop Bil.arshift (Bil.var y) two in
  let block = Blk.create ()
              |> mk_def x (Bil.int @@ Word.of_int 0x20000000 ~width:32)
              |> mk_def y (Bil.var x)
              |> mk_def y lshift
              |> mk_def y rshift
  in
  let post = Bool.mk_eq ctx (mk_z3_var env y) (mk_z3_var env x)
             |> Constr.mk_goal "y = x"
             |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_block env post block in
  assert_z3_result test_ctx env (Blk.to_string block) post pre Z3.Solver.SATISFIABLE


let test_ite_assign_1 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env = Pre.mk_env ctx var_gen  in
  let x = Var.create "x" reg8_t in
  let y = Var.create "y" reg8_t in
  let lshift = Bil.binop Bil.lshift (Bil.var x) (Bil.int @@ Word.one 8) in
  let rshift = Bil.binop Bil.arshift lshift (Bil.int @@ Word.one 8) in
  let lt = Bil.binop Bil.lt (Bil.var x) (Bil.int @@ Word.of_int 0x40 ~width:8) in
  let ite = Bil.ite ~if_:lt ~then_:rshift ~else_:(Bil.var x) in
  let block = Blk.create ()
              |> mk_def y ite
  in
  let post = Bool.mk_eq ctx (mk_z3_var env y) (mk_z3_var env x)
             |> Constr.mk_goal "y = x"
             |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_block env post block in
  assert_z3_result test_ctx env (Blk.to_string block) post pre Z3.Solver.UNSATISFIABLE


let test_subroutine_1 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env = Pre.mk_env ctx var_gen  in
  let x = Var.create "x" reg32_t in
  let y = Var.create "y" reg32_t in
  let z = Var.create "z" reg32_t in

  let sub = Bil.(
      [ if_ ((var x) < (i32 10))
          [y := (var x) + (i32 1)]
          [y := (var x) - (i32 1)];
        z := var y
      ]
    ) |> bil_to_sub
  in

  let diff = mk_z3_expr env Bil.((var z) - (var x)) in
  let high  = BV.mk_sle ctx diff (BV.mk_numeral ctx "1" 32) in
  let low = BV.mk_sle ctx (BV.mk_numeral ctx "-1" 32) diff in
  let post = Bool.mk_and ctx [low; high]
             |> Constr.mk_goal "-1 <= z - x && z - x <= 1"
             |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_sub env post sub in
  assert_z3_result test_ctx env (Sub.to_string sub) post pre Z3.Solver.UNSATISFIABLE


let test_subroutine_1_2 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env = Pre.mk_env ctx var_gen  in
  let x = Var.create "x" reg32_t in
  let y = Var.create "y" reg32_t in
  let z = Var.create "z" reg32_t in

  let sub = Bil.(
      [ if_ ((var x) < (i32 10))
          [y := (var x) + (i32 1)]
          [y := (var x) - (i32 1)];
        z := var y
      ]
    ) |> bil_to_sub
  in
  (* We have to manually add the names x, y, z to the environment *)
  let env = Env.add_var env x (mk_z3_var env x) in
  let env = Env.add_var env y (mk_z3_var env y) in
  let env = Env.add_var env z (mk_z3_var env z) in
  (* Converting the smtlib string to a Constr.t should properly rename x, y, and z to
     x0, y0, and z0 respectively. *)
  let post = Z3_utils.mk_smtlib2_single env
      "(assert (and (bvsle (bvsub z x) #x00000001) (bvsle #xffffffff (bvsub z x))))"
  in
  let pre, _ = Pre.visit_sub env post sub in
  assert_z3_result test_ctx env (Sub.to_string sub) post pre Z3.Solver.UNSATISFIABLE


let test_subroutine_2 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env = Pre.mk_env ctx var_gen  in
  let l1_tid = Tid.create () in
  let l2_tid = Tid.create () in
  let l3_tid = Tid.create () in
  let l4_tid = Tid.create () in
  Tid.set_name l1_tid "test_l1";
  Tid.set_name l2_tid "test_l2";
  Tid.set_name l3_tid "test_l3";
  Tid.set_name l4_tid "test_l4";
  let blk1 = Blk.create () ~tid:l1_tid in
  let blk2 = Blk.create () ~tid:l2_tid in
  let blk3 = Blk.create () ~tid:l3_tid in
  let blk4 = Blk.create () ~tid:l4_tid in
  let x1 = Var.create "x1" reg32_t in
  let x2 = Var.create "x2" reg32_t in
  let x3 = Var.create "x3" reg32_t in
  let x4 = Var.create "x4" reg32_t in
  let lt = Bil.binop Bil.lt (Bil.var x1) (Bil.int @@ Word.of_int 10 ~width:32) in
  let e2 = Bil.binop Bil.plus (Bil.var x1) one in
  let e3 = Bil.binop Bil.minus (Bil.var x1) one in
  let phi_x = Phi.of_list x4 [(l2_tid, Bil.var x2); (l3_tid, Bil.var x3)] in
  let blk1 = blk1 |> mk_cond lt blk2 blk3 in
  let blk2 = blk2
             |> mk_def x2 e2
             |> mk_jmp blk4
  in
  let blk3 = blk3
             |> mk_def x3 e3
             |> mk_jmp blk4
  in
  let blk4 = blk4 |> mk_phi phi_x in
  let sub = mk_sub [blk1; blk2; blk3; blk4] in
  let diff = mk_z3_expr env (Bil.binop Bil.minus (Bil.var x4) (Bil.var x1)) in
  let high  = BV.mk_sle ctx diff (BV.mk_numeral ctx "1" 32) in
  let low = BV.mk_sle ctx (BV.mk_numeral ctx "-1" 32) diff in
  let post = Bool.mk_and ctx [low; high]
             |> Constr.mk_goal "x4 - x1 <= 1 && -1 <= x4 - x1"
             |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_sub env post sub in
  assert_z3_result test_ctx env (Sub.to_string sub) post pre Z3.Solver.UNSATISFIABLE


let test_subroutine_3 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env = Pre.mk_env ctx var_gen  in
  let x = Var.create "x" reg32_t in
  let y = Var.create "y" reg32_t in
  let z = Var.create "z" reg32_t in
  let sub = Bil.(
      [ if_ ( (var x) <= (i32 0) )
          [x := var y]
          [x := var z]
      ]
    ) |> bil_to_sub
  in
  let y_exp = Bool.mk_eq ctx (mk_z3_var env x) (mk_z3_var env y) in
  let z_exp = Bool.mk_eq ctx (mk_z3_var env x) (mk_z3_var env z) in
  let post = Bool.mk_or ctx [y_exp; z_exp]
             |> Constr.mk_goal "x = y || x = z"
             |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_sub env post sub in
  assert_z3_result test_ctx env (Sub.to_string sub) post pre Z3.Solver.UNSATISFIABLE


let test_subroutine_4 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env = Pre.mk_env ctx var_gen  in
  let blk1 = Blk.create () in
  let blk2 = Blk.create () in
  let blk3 = Blk.create () in
  let x = Var.create "x" reg32_t in
  let y = Var.create "y" reg32_t in
  let z = Var.create "z" reg32_t in
  let w = Var.create "w" reg32_t in
  let blk1 = blk1
             |> mk_def x (Bil.var y)
             |> mk_jmp blk3
  in
  let blk2 = blk2
             |> mk_def x (Bil.var z)
             |> mk_jmp blk3
  in
  let blk3 = blk3 |> mk_def w (Bil.var x) in
  let sub = mk_sub [blk1; blk2; blk3] in
  let y_exp = Bool.mk_eq ctx (mk_z3_var env w) (mk_z3_var env y) in
  let z_exp = Bool.mk_eq ctx (mk_z3_var env w) (mk_z3_var env z) in
  let post = Bool.mk_or ctx [y_exp; z_exp]
             |> Constr.mk_goal "x = y || w = z"
             |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_sub env post sub in
  assert_z3_result test_ctx env (Sub.to_string sub) post pre Z3.Solver.UNSATISFIABLE


let test_subroutine_5 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env = Pre.mk_env ctx var_gen  in
  let blk1 = Blk.create () in
  let blk2 = Blk.create () in
  let blk3 = Blk.create () in
  let x = Var.create "x" reg32_t in
  let y = Var.create "y" reg32_t in
  let z = Var.create "z" reg32_t in
  let e = Bil.((var x) + (i32 1)) in
  let e' = Bil.((var y) + (i32 1)) in
  let blk1 = blk1
             |> mk_def x (Bil.var y)
             |> mk_call (Label.direct (Term.tid blk2)) (Label.direct (Tid.create ()))
  in
  let blk2 = blk2 |> mk_def x e |> mk_jmp blk3 in
  let blk3 = blk3 |> mk_def z (Bil.var x) in
  let sub = mk_sub [blk1; blk2; blk3] in
  let post = Bool.mk_eq ctx (mk_z3_var env z) (mk_z3_expr env e')
             |> Constr.mk_goal "z = y + 1"
             |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_sub env post sub in
  assert_z3_result test_ctx env (Sub.to_string sub) post pre Z3.Solver.UNSATISFIABLE


let test_subroutine_6 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let assert_tid = Tid.create () in
  Tid.set_name assert_tid "__assert_fail";
  let blk1 = Blk.create () in
  let blk2 = Blk.create () in
  let blk3 = Blk.create () in
  let sub_assert = mk_sub ~tid:assert_tid ~name:"__assert_fail" [blk1] in
  let blk2 = blk2 |> mk_call (Label.direct (Term.tid blk3)) (Label.direct (Term.tid sub_assert)) in
  let sub = mk_sub [blk2; blk3] in
  let subs = Seq.of_list [sub; sub_assert] in
  let env = Pre.mk_env ~subs ctx var_gen in
  let post = true_constr ctx in
  let pre, _ = Pre.visit_sub env post sub in
  assert_z3_result test_ctx env (Sub.to_string sub) post pre Z3.Solver.SATISFIABLE


let test_subroutine_7 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let assert_sub, assert_expr = Bil_to_bir.mk_assert_fail () in
  let sub = Bil_to_bir.bil_to_sub Bil.([jmp assert_expr])  in
  let subs = Seq.singleton assert_sub in
  let env = Pre.mk_env ~subs ctx var_gen in
  let post = true_constr ctx in
  let pre, _ = Pre.visit_sub env post sub in
  assert_z3_result test_ctx env (Sub.to_string sub) post pre Z3.Solver.SATISFIABLE


let test_call_1 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let sub_tid = Tid.create () in
  Tid.set_name sub_tid "test_sub";
  let blk1 = Blk.create () in
  let blk2 = Blk.create () in
  let blk3 = Blk.create () in
  let ret_var = Var.create "ret" reg32_t in
  let dummy_var = Var.create "dummy" reg32_t in
  let call_body = mk_sub ~tid:sub_tid
      ~args:[Bap.Std.Arg.create ~intent:Bap.Std.Out dummy_var (Bil.var ret_var)]
      ~name:"test_sub" [blk1] in
  let blk2 = blk2
             |> mk_def ret_var zero
             |> mk_call (Label.direct (Term.tid blk3)) (Label.direct (Term.tid call_body)) in
  let main_sub = mk_sub [blk2; blk3] in
  let env = Pre.mk_env ctx var_gen 
      ~subs:(Seq.of_list [call_body; main_sub]) in
  let post = Bool.mk_eq ctx (mk_z3_expr env (Bil.var ret_var)) (mk_z3_expr env zero)
             |> Constr.mk_goal "ret = 0"
             |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_sub env post main_sub in
  assert_z3_result test_ctx env (Sub.to_string main_sub) post pre Z3.Solver.SATISFIABLE


let test_call_2 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let sub_tid = Tid.create () in
  Tid.set_name sub_tid "test_sub";
  let blk1 = Blk.create () in
  let blk2 = Blk.create () in
  let blk3 = Blk.create () in
  let ret_var = Var.create "ret" reg32_t in
  let dummy_var = Var.create "dummy" reg32_t in
  let call_body = mk_sub ~tid:sub_tid
      ~args:[Bap.Std.Arg.create ~intent:Bap.Std.Out dummy_var (Bil.var ret_var)]
      ~name:"test_sub" [blk1] in
  let blk2 = blk2
             |> mk_def ret_var zero
             |> mk_call (Label.direct (Term.tid blk3)) (Label.direct (Term.tid call_body)) in
  let main_sub = mk_sub [blk2; blk3] in
  let env = Pre.mk_env ctx var_gen  ~subs:(Seq.of_list [call_body; main_sub]) in
  let post = Bool.mk_const_s ctx "called_test_sub1"
             |> Constr.mk_goal "called_test_sub1"
             |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_sub env post main_sub in
  assert_z3_result test_ctx env (Sub.to_string main_sub) post pre Z3.Solver.UNSATISFIABLE


let test_call_3 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let sub_tid = Tid.create () in
  Tid.set_name sub_tid "test_sub";
  let blk1 = Blk.create () in
  let blk2 = Blk.create () in
  let blk3 = Blk.create () in
  let ret_var = Var.create "RAX" reg32_t in
  let blk1 = blk1 |> mk_def ret_var zero in
  let call_body = mk_sub ~tid:sub_tid ~name:"test_sub" [blk1] in
  let blk2 = blk2 |> mk_call (Label.direct (Term.tid blk3)) (Label.direct (Term.tid call_body)) in
  let main_sub = mk_sub [blk2; blk3] in
  let env = Pre.mk_env ctx var_gen  ~subs:(Seq.of_list [call_body; main_sub]) in
  let post = Bool.mk_const_s ctx "called_test_sub1"
             |> Constr.mk_goal "called_test_sub1"
             |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_sub env post main_sub in
  assert_z3_result test_ctx env (Sub.to_string main_sub) post pre Z3.Solver.UNSATISFIABLE


let test_call_4 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let sub_tid = Tid.create () in
  Tid.set_name sub_tid "test_sub";
  let blk1 = Blk.create () in
  let blk2 = Blk.create () in
  let blk3 = Blk.create () in
  let call_body = mk_sub ~tid:sub_tid ~name:"test_sub" [blk1] in
  let blk2 = blk2 |> mk_call (Label.direct (Term.tid blk3)) (Label.direct (Term.tid call_body)) in
  let main_sub = mk_sub [blk2; blk3] in
  let env = Pre.mk_env ctx var_gen  ~subs:(Seq.of_list [call_body; main_sub]) in
  let post = Bool.mk_const_s ctx "called_test_sub1"
             |> Constr.mk_goal "called_test_sub1"
             |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_sub env post main_sub in
  assert_z3_result test_ctx env (Sub.to_string main_sub) post pre Z3.Solver.UNSATISFIABLE


let test_call_5 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let sub_tid = Tid.create () in
  Tid.set_name sub_tid "test_sub";
  let start_body = Blk.create () in
  let x = Var.create "x" reg32_t in
  let blk1 = Blk.create () in
  let blk2 = Blk.create () in
  let blk3 = Blk.create () in
  let cond = Bil.((var x) = (i32 1)) in
  let call_body = mk_sub ~tid:sub_tid ~name:"test_sub" [blk1] in
  let start_body = start_body
                   |> mk_def x zero
                   |> mk_cond cond blk2 blk3 in
  let blk2 = blk2 |> mk_call (Label.direct (Term.tid blk3)) (Label.direct (Term.tid call_body)) in
  let main_sub = mk_sub [start_body; blk2; blk3] in
  let env = Pre.mk_env ctx var_gen  ~subs:(Seq.of_list [call_body; main_sub]) in
  let post = Bool.mk_const_s ctx "called_test_sub1"
             |> Constr.mk_goal "called_test_sub1"
             |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_sub env post main_sub in
  assert_z3_result test_ctx env (Sub.to_string main_sub) post pre Z3.Solver.SATISFIABLE


let test_call_6 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let sub1_tid = Tid.create () in
  Tid.set_name sub1_tid "test_sub1";
  let sub2_tid = Tid.create () in
  Tid.set_name sub2_tid "test_sub2";
  let start_body = Blk.create () in
  let x = Var.create "x" reg32_t in
  let blk1 = Blk.create () in
  let blk2 = Blk.create () in
  let blk3 = Blk.create () in
  let blk4 = Blk.create () in
  let cond = Bil.((var x) = (i32 1)) in
  let call1_body = mk_sub ~tid:sub1_tid ~name:"test_sub1" [blk1] in
  let call2_body = mk_sub ~tid:sub2_tid ~name:"test_sub2" [blk1] in
  let start_body = start_body |> mk_cond cond blk2 blk3 in
  let blk2 = blk2 |> mk_call (Label.direct (Term.tid blk4)) (Label.direct (Term.tid call1_body)) in
  let blk3 = blk3 |> mk_call (Label.direct (Term.tid blk4)) (Label.direct (Term.tid call2_body)) in
  let main_sub = mk_sub [start_body; blk2; blk3; blk4] in
  let env = Pre.mk_env ctx var_gen 
      ~subs:(Seq.of_list [call1_body; call2_body; main_sub]) in
  let sub1_called = Option.value_exn (sub1_tid |> Env.get_called env) in
  let sub2_called = Option.value_exn (sub2_tid |> Env.get_called env) in
  let post =
    Bool.mk_or ctx [Bool.mk_const_s ctx sub1_called; Bool.mk_const_s ctx sub2_called]
    |> Constr.mk_goal "sub1_called || sub2_called"
    |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_sub env post main_sub in
  assert_z3_result test_ctx env (Sub.to_string main_sub) post pre Z3.Solver.UNSATISFIABLE


let test_call_7 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let call_tid = Tid.create () in
  Tid.set_name call_tid "call_sub";
  let blk1 = Blk.create () in
  let blk2 = Blk.create () in
  let blk3 = Blk.create () in
  let x = Var.create "x" reg32_t in
  let y = Var.create "y" reg32_t in
  let z = Var.create "z" reg32_t in
  let call_in = Var.create "call_in" reg32_t in
  let call_out = Var.create "call_out" reg32_t in
  let args = [Bap.Std.Arg.create ~intent:Bap.Std.In call_in (Bil.var x);
              Bap.Std.Arg.create ~intent:Bap.Std.Out call_out (Bil.var y)] in
  let blk1 = blk1 |> mk_def y Bil.(var x + one) in
  let call_sub = mk_sub ~args ~tid:call_tid ~name:"call_sub" [blk1] in
  let blk2 = blk2
             |> mk_call (Label.direct (Term.tid blk3))
               (Label.direct (Term.tid call_sub)) in
  let blk3 = blk3 |> mk_def z (Bil.var y) in
  let main_sub = mk_sub [blk2; blk3] in
  let env = Pre.mk_env ctx var_gen
      ~subs:(Seq.of_list [main_sub; call_sub])
      ~to_inline:(Seq.singleton call_sub)
  in
  let sub_called = Option.value_exn (call_tid |> Env.get_called env) in
  let post = Bool.mk_and ctx [
      Bool.mk_eq ctx (mk_z3_expr env Bil.(var x + one)) (mk_z3_expr env (Bil.var z));
      Bool.mk_const_s ctx sub_called]
             |> Constr.mk_goal "x + 1 = z && sub_called"
             |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_sub env post main_sub in
  let fmtr = (Sub.to_string main_sub) ^ (Sub.to_string call_sub) in
  assert_z3_result test_ctx env fmtr post pre Z3.Solver.UNSATISFIABLE


let test_call_8 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let call_tid = Tid.create () in
  Tid.set_name call_tid "call_sub";
  let blk1 = Blk.create () in
  let blk2 = Blk.create () in
  let blk3 = Blk.create () in
  let x = Var.create "x" reg32_t in
  let y = Var.create "y" reg32_t in
  let z = Var.create "z" reg32_t in
  let call_in = Var.create "call_in" reg32_t in
  let call_out = Var.create "call_out" reg32_t in
  let args = [Bap.Std.Arg.create ~intent:Bap.Std.In call_in (Bil.var x);
              Bap.Std.Arg.create ~intent:Bap.Std.Out call_out (Bil.var y)] in
  let blk1 = blk1 |> mk_def y Bil.(var x + one) in
  let call_sub = mk_sub ~args ~tid:call_tid ~name:"call_sub" [blk1] in
  let blk2 = blk2
             |> mk_call (Label.direct (Term.tid blk3))
               (Label.direct (Term.tid call_sub)) in
  let blk3 = blk3 |> mk_def z (Bil.var y) in
  let main_sub = mk_sub [blk2; blk3] in
  let env = Pre.mk_env ctx var_gen  ~subs:(Seq.of_list [main_sub; call_sub]) in
  let sub_called = Option.value_exn (call_tid |> Env.get_called env) in
  let post = Bool.mk_and ctx [
      Bool.mk_eq ctx (mk_z3_expr env Bil.(var x + one)) (mk_z3_expr env (Bil.var z));
      Bool.mk_const_s ctx sub_called]
             |> Constr.mk_goal "x + 1 = z && sub_called"
             |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_sub env post main_sub in
  let fmtr = (Sub.to_string main_sub) ^ (Sub.to_string call_sub) in
  assert_z3_result test_ctx env fmtr post pre Z3.Solver.SATISFIABLE

let test_call_9 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let call1_tid = Tid.create () in
  Tid.set_name call1_tid "call1_sub";
  let call2_tid = Tid.create () in
  Tid.set_name call2_tid "call2_sub";
  let blk1 = Blk.create () in
  let blk1' = Blk.create () in
  let blk2 = Blk.create () in
  let blk_main = Blk.create () in
  let blk_main' = Blk.create () in
  let x = Var.create "x" reg32_t in
  let y = Var.create "y" reg32_t in
  let z = Var.create "z" reg32_t in
  let blk2 = blk2 |> mk_def z Bil.(var y + one) in
  let call2_sub = mk_sub ~tid:call2_tid ~name:"call2_sub" [blk2] in
  let blk1 = blk1
             |> mk_def y Bil.(var x + one)
             |> mk_call (Label.direct (Term.tid blk1'))
               (Label.direct (Term.tid call2_sub))
  in
  let call1_sub = mk_sub ~tid:call1_tid ~name:"call1_sub" [blk1; blk1'] in
  let blk_main = blk_main
                 |> mk_call (Label.direct (Term.tid blk_main'))
                   (Label.direct (Term.tid call1_sub)) in
  let main_sub = mk_sub [blk_main; blk_main'] in
  let env = Pre.mk_env ctx var_gen
      ~subs:(Seq.of_list [main_sub; call1_sub; call2_sub])
      ~to_inline:(Seq.of_list [call1_sub; call2_sub])
  in
  let sub1_called = Option.value_exn (call1_tid |> Env.get_called env) in
  let sub2_called = Option.value_exn (call2_tid |> Env.get_called env) in
  let post = Bool.mk_and ctx [
      Bool.mk_eq ctx (mk_z3_expr env Bil.(var x + two)) (mk_z3_expr env (Bil.var z));
      Bool.mk_const_s ctx sub1_called;
      Bool.mk_const_s ctx sub2_called]
             |> Constr.mk_goal "x + 2 = z && sub1_called && sub2_called"
             |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_sub env post main_sub in
  let fmtr = (Sub.to_string main_sub) ^ (Sub.to_string call1_sub) ^ (Sub.to_string call2_sub) in
  assert_z3_result test_ctx env fmtr post pre Z3.Solver.UNSATISFIABLE

let test_call_10 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let call1_tid = Tid.create () in
  Tid.set_name call1_tid "call1_sub";
  let call2_tid = Tid.create () in
  Tid.set_name call2_tid "call2_sub";
  let blk1 = Blk.create () in
  let blk1' = Blk.create () in
  let blk2 = Blk.create () in
  let blk_main = Blk.create () in
  let blk_main' = Blk.create () in
  let x = Var.create "x" reg32_t in
  let y = Var.create "y" reg32_t in
  let z = Var.create "z" reg32_t in
  let blk2 = blk2 |> mk_def z Bil.(var y + one) in
  let call2_sub = mk_sub ~tid:call2_tid ~name:"call2_sub" [blk2] in
  let blk1 = blk1
             |> mk_def y Bil.(var x + one)
             |> mk_call (Label.direct (Term.tid blk1'))
               (Label.direct (Term.tid call2_sub))
  in
  let call1_sub = mk_sub ~tid:call1_tid ~name:"call1_sub" [blk1; blk1'] in
  let blk_main = blk_main
                 |> mk_call (Label.direct (Term.tid blk_main'))
                   (Label.direct (Term.tid call1_sub)) in
  let main_sub = mk_sub [blk_main; blk_main'] in
  let env = Pre.mk_env ctx var_gen
      ~subs:(Seq.of_list [main_sub; call1_sub; call2_sub])
      ~to_inline:(Seq.of_list [call1_sub])
  in
  let sub1_called = Option.value_exn (call1_tid |> Env.get_called env) in
  let sub2_called = Option.value_exn (call2_tid |> Env.get_called env) in
  let post = Bool.mk_and ctx [
      Bool.mk_eq ctx (mk_z3_expr env Bil.(var x + two)) (mk_z3_expr env (Bil.var z));
      Bool.mk_const_s ctx sub1_called;
      Bool.mk_const_s ctx sub2_called]
             |> Constr.mk_goal "x + 2 = z && sub1_called && sub2_called"
             |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_sub env post main_sub in
  let fmtr = (Sub.to_string main_sub) ^ (Sub.to_string call1_sub) ^ (Sub.to_string call2_sub) in
  assert_z3_result test_ctx env fmtr post pre Z3.Solver.SATISFIABLE

let test_int_1 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let blk1 = Blk.create () in
  let blk2 = Blk.create () in
  let ret_var = Var.create "ret" reg32_t in
  let blk1 = blk1
             |> mk_def ret_var zero
             |> mk_int 0x0 blk2
  in
  let main_sub = mk_sub [blk1; blk2] in
  let env = Pre.mk_env ctx var_gen ~to_inline:(Seq.empty) ~subs:(Seq.of_list [main_sub]) in
  let post = Bool.mk_eq ctx (mk_z3_expr env (Bil.var ret_var)) (mk_z3_expr env zero)
             |> Constr.mk_goal "ret = 0"
             |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_sub env post main_sub in
  assert_z3_result test_ctx env (Sub.to_string main_sub) post pre Z3.Solver.UNSATISFIABLE


let test_loop_1 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env = Pre.mk_env ctx var_gen  in
  let x = Var.create "x" reg32_t in
  let y = Var.create "y" reg32_t in
  let a = Var.create "a" reg32_t in
  let b = Var.create "b" reg32_t in
  let x_y = Bil.( var x + var y) in
  let a_b = Bil.( var a + var b) in
  let sub = Bil.(
      [
        x := var a;
        y := var b;
        while_ (lnot (var y <= zero) )
          [
            x := var x + one;
            y := var y - one;
          ]
      ]
    ) |> bil_to_sub
  in

  let post = Bool.mk_eq ctx (mk_z3_expr env x_y) (mk_z3_expr env a_b)
             |> Constr.mk_goal "x + y = a + b"
             |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_sub env post sub in
  assert_z3_result test_ctx env (Sub.to_string sub) post pre Z3.Solver.UNSATISFIABLE


let test_loop_2 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env = Pre.mk_env ctx var_gen in
  let x = Var.create "x" reg32_t in
  let y = Var.create "y" reg32_t in
  let sub = Bil.(
      [
        x := zero;
        y := i32 5;
        while_ ( var y > zero )
          [
            x := var x + one;
            y := var y - one;
          ]
      ]
    ) |> bil_to_sub
  in
  let post = Bool.mk_eq ctx (mk_z3_var env x) (BV.mk_numeral ctx "5" 32)
             |> Constr.mk_goal "x = 5"
             |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_sub env post sub in
  assert_z3_result test_ctx env (Sub.to_string sub) post pre Z3.Solver.UNSATISFIABLE


let test_loop_3 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env = Pre.mk_env ctx var_gen  in
  let x = Var.create "x" reg32_t in
  let y = Var.create "y" reg32_t in
  let sub = Bil.(
      [
        x := zero;
        y := i32 7;
        while_ ( var y > zero )
          [
            x := var x + one;
            y := var y - one;
          ]
      ]
    ) |> bil_to_sub
  in
  let post = Bool.mk_eq ctx (mk_z3_var env x) (BV.mk_numeral ctx "7" 32)
             |> Constr.mk_goal "x = 7"
             |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_sub env post sub in
  assert_z3_result test_ctx env (Sub.to_string sub) post pre Z3.Solver.SATISFIABLE


let test_loop_4 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env = Pre.mk_env ~num_loop_unroll:1 ctx var_gen in
  let x = Var.create "x" reg32_t in
  let y = Var.create "y" reg32_t in
  let sub = Bil.(
      [
        x := zero;
        y := i32 2;
        while_ ( var y > zero )
          [
            x := var x + one;
            y := var y - one;
          ]
      ]
    ) |> bil_to_sub
  in
  let post = Bool.mk_eq ctx (mk_z3_var env x) (BV.mk_numeral ctx "2" 32)
             |> Constr.mk_goal "x = 2"
             |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_sub env post sub in
  assert_z3_result test_ctx env (Sub.to_string sub) post pre Z3.Solver.UNSATISFIABLE


let test_loop_5 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env = Pre.mk_env ctx var_gen ~num_loop_unroll:1 in
  let x = Var.create "x" reg32_t in
  let y = Var.create "y" reg32_t in
  let sub = Bil.(
      [
        x := zero;
        y := i32 1;
        while_ ( var y > zero )
          [
            x := var x + one;
            y := var y - one;
          ];
        x := var x + i32 2;
      ]
    ) |> bil_to_sub
  in
  let post = Bool.mk_eq ctx (mk_z3_var env x) (BV.mk_numeral ctx "3" 32)
             |> Constr.mk_goal "x = 3"
             |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_sub env post sub in
  assert_z3_result test_ctx env (Sub.to_string sub) post pre Z3.Solver.UNSATISFIABLE


let test_loop_6 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env = Pre.mk_env ctx var_gen ~num_loop_unroll:1 in
  let x = Var.create "x" reg32_t in
  let y = Var.create "y" reg32_t in
  let start = Blk.create () in
  let loop_header = Blk.create () in
  let loop_body = Blk.create () in
  let exit = Blk.create () in
  let start = start
              |> mk_def x zero
              |> mk_def y (i32 1)
              |> mk_jmp loop_header
  in
  let loop_header = loop_header
                    |> mk_cond Bil.((zero < var y)) loop_body exit
  in
  let loop_body = loop_body
                  |> mk_def x Bil.(var x + one)
                  |> mk_def y Bil.(var y - one)
                  |> mk_jmp loop_header
  in
  let exit = exit
             |> mk_def x Bil.(var x + i32 2)
  in
  let sub = mk_sub [start; loop_header; loop_body; exit] in
  let post = Bool.mk_eq ctx (mk_z3_var env x) (BV.mk_numeral ctx "3" 32)
             |> Constr.mk_goal "x = 3"
             |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_sub env post sub in
  assert_z3_result test_ctx env (Sub.to_string sub) post pre Z3.Solver.UNSATISFIABLE


(* Currently only testing expressions that evaluate to immediates. *)
let eval_to_int (exp : exp) : int =
  match Exp.eval exp with
  | Bil.Imm word -> Word.to_int_exn word
  | Bil.Mem _ -> assert false
  | Bil.Bot -> assert false


let test_cast (width_orig : int) (width_cast : int) (value : int)
    (cast : Bil.cast) (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env = Pre.mk_env ctx var_gen  in
  let bil_var = Bil.int @@ Word.of_int value ~width:width_orig in
  let bil_cast = Bil.cast cast width_cast bil_var in
  let z3_var = Expr.simplify (mk_z3_expr env bil_var) None in
  let z3_cast = Expr.simplify (mk_z3_expr env bil_cast) None in
  let sort_var = Expr.get_sort z3_var in
  let sort_cast = Expr.get_sort z3_cast in
  let bil_var' = eval_to_int bil_var in
  let bil_cast' = eval_to_int bil_cast in
  assert_equal ~ctxt:test_ctx ~cmp:Expr.equal ~printer:Expr.to_string
    z3_var (Expr.mk_numeral_int ctx bil_var' sort_var);
  assert_equal ~ctxt:test_ctx ~cmp:Expr.equal ~printer:Expr.to_string
    z3_cast (Expr.mk_numeral_int ctx bil_cast' sort_cast);
  assert_equal ~ctxt:test_ctx ~printer:string_of_int width_orig (BV.get_size sort_var);
  assert_equal ~ctxt:test_ctx ~printer:string_of_int width_cast (BV.get_size sort_cast)


let test_shift_bitwidth (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let x = Var.create "x" reg32_t in
  let y = Var.create "y" reg32_t in
  let two = Bil.int @@ Word.of_int ~width:2 2 in
  let sub = Bil.(
      [
        x := i32 0x3fffffff;
        y := var x lsl two;
        y := var y lsr two;
      ]
    ) |> bil_to_sub
  in
  let env = Pre.mk_env ctx var_gen ~subs:(Seq.singleton sub) in
  let post =
    Bool.mk_eq ctx (mk_z3_var env x) (mk_z3_var env y)
    |> Constr.mk_goal "x = y"
    |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_sub env post sub in
  assert_z3_result test_ctx env (Sub.to_string sub) post pre Z3.Solver.UNSATISFIABLE


let test_exp_cond_1 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env = Pre.mk_env ctx var_gen  ~exp_conds:[Pre.non_null_load_vc] in
  let blk = Blk.create () in
  let addr = Var.create "addr" reg32_t in
  let mem = Var.create "mem" (mem32_t `r8) in
  let x = Var.create "x" reg8_t in
  let load = Bil.load ~mem:(Bil.var mem) ~addr:(Bil.var addr) BigEndian `r8 in
  let blk = blk |> mk_def x load in
  let post = true_constr ctx in
  let pre, _ = Pre.visit_block env post blk in
  assert_z3_result test_ctx env (Blk.to_string blk) post pre Z3.Solver.SATISFIABLE


let test_exp_cond_2 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env = Pre.mk_env ctx var_gen  ~exp_conds:[Pre.non_null_load_vc] in
  let blk = Blk.create () in
  let addr = Var.create "addr" reg32_t in
  let mem = Var.create "mem" (mem32_t `r8) in
  let x = Var.create "x" reg8_t in
  let load = Bil.load ~mem:(Bil.var mem) ~addr:(Bil.var addr) BigEndian `r8 in
  let blk = blk
            |> mk_def addr (Bil.int @@ Word.of_int 0x40000000 ~width:32)
            |> mk_def x load in
  let post = true_constr ctx in
  let pre, _ = Pre.visit_block env post blk in
  assert_z3_result test_ctx env (Blk.to_string blk) post pre Z3.Solver.UNSATISFIABLE


let test_subroutine_8 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env = Pre.mk_env ctx var_gen  ~exp_conds:[Pre.non_null_load_assert] in
  let mem = Var.create "mem" (mem32_t `r32) in
  let loc = Var.create "loc" reg32_t in
  let read = Bil.(load ~mem:(var mem) ~addr:(var loc) LittleEndian `r32) in
  let sub = Bil.([if_ (read = i32 12)[][]]) |> bil_to_sub in
  let post = Bool.mk_distinct ctx [(mk_z3_var env loc); (BV.mk_numeral ctx "0" 32)]
             |> Constr.mk_goal "loc <> 0"
             |> Constr.mk_constr
  in
  let pre, _ = Pre. visit_sub env post sub in
  assert_z3_result test_ctx env (Sub.to_string sub) post pre Z3.Solver.UNSATISFIABLE


let test_branches_1 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let x = Var.create "x" reg32_t in
  let y = Var.create "y" reg32_t in
  let z = Var.create "z" reg32_t in
  let cond_x = Bil.(var x = i32 2) in
  let cond_y = Bil.(var y = i32 3) in
  let cond_z = Bil.(var z = i32 4) in
  let sub = Bil.(
      [ if_ (cond_x)
          [ if_ (cond_y)
              [ if_ (cond_z)
                  []
                  []
              ]
              []
          ]
          []
      ]
    ) |> bil_to_sub
  in
  let jmp_spec = fun env post _ jmp ->
    let jump_cond cond = Pre.bv_to_bool (mk_z3_expr env cond) ctx 1 in
    let jump_pre =
      match Jmp.kind jmp with
      | Goto (Direct tid) -> Option.value (Env.get_precondition env tid) ~default:post
      | _ -> assert false
    in
    if Jmp.equal jmp (find_jump sub cond_x) then
      Some (Constr.mk_ite jmp (jump_cond cond_x) jump_pre (true_constr ctx), env)
    else if Jmp.equal jmp (find_jump sub cond_y) then
      Some (Constr.mk_ite jmp (jump_cond cond_y) jump_pre (true_constr ctx), env)
    else if Jmp.equal jmp (find_jump sub cond_z) then
      Some (Constr.mk_ite jmp (jump_cond cond_z) (false_constr ctx) (true_constr ctx), env)
    else
      None
  in
  let env = Pre.mk_env ctx var_gen  ~jmp_spec ~subs:(Seq.singleton sub) in
  let post = true_constr ctx in
  let pre, _ = Pre.visit_sub env post sub in
  assert_z3_result test_ctx env (Sub.to_string sub) post pre Z3.Solver.SATISFIABLE


let test_jmp_spec_reach_1 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let x = Var.create "x" reg32_t in
  let y = Var.create "y" reg32_t in
  let z = Var.create "z" reg32_t in
  let cond_x = Bil.(var x = i32 2) in
  let cond_y = Bil.(var y = i32 3) in
  let cond_z = Bil.(var z = i32 4) in
  let sub = Bil.(
      [ if_ (cond_x)
          [ if_ (cond_y)
              [ if_ (cond_z)
                  []
                  []
              ]
              []
          ]
          []
      ]
    ) |> bil_to_sub
  in
  let jmp_spec =
    Jmp.Map.empty
    |> Jmp.Map.set ~key:(find_jump sub cond_x) ~data:true
    |> Jmp.Map.set ~key:(find_jump sub cond_y) ~data:true
    |> Jmp.Map.set ~key:(find_jump sub cond_z) ~data:false
    |> Pre.jmp_spec_reach
  in
  let env = Pre.mk_env ctx var_gen  ~jmp_spec ~subs:(Seq.singleton sub) in
  let post = true_constr ctx in
  let pre, _ = Pre.visit_sub env post sub in
  let solver = Z3.Solver.mk_simple_solver ctx in
  let result = Pre.check ~refute:false solver ctx pre in
  assert_equal ~ctxt:test_ctx ~printer:Z3.Solver.string_of_status
    Z3.Solver.SATISFIABLE result;
  let model = Constr.get_model_exn solver in
  assert_equal ~ctxt:test_ctx ~printer:Expr.to_string
    (jump_taken ctx) (cond_x |> mk_z3_expr env |> Constr.eval_model_exn model);
  assert_equal ~ctxt:test_ctx ~printer:Expr.to_string
    (jump_taken ctx) (cond_y |> mk_z3_expr env |> Constr.eval_model_exn model);
  assert_equal ~ctxt:test_ctx ~printer:Expr.to_string
    (jump_not_taken ctx) (cond_z |> mk_z3_expr env |> Constr.eval_model_exn model)


let test_jmp_spec_reach_2 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let x = Var.create "x" reg32_t in
  let y = Var.create "y" reg32_t in
  let cond_x = Bil.(var x = i32 2) in
  let cond_y = Bil.(var y = i32 3) in
  let cond_unsat = Bil.(var x + var y <> i32 5) in
  let sub = Bil.(
      [ if_ (cond_x)
          [ if_ (cond_y)
              [ if_ (cond_unsat)
                  []
                  []
              ]
              []
          ]
          []
      ]
    ) |> bil_to_sub
  in
  let jmp_spec =
    Jmp.Map.empty
    |> Jmp.Map.set ~key:(find_jump sub cond_x) ~data:true
    |> Jmp.Map.set ~key:(find_jump sub cond_y) ~data:true
    |> Jmp.Map.set ~key:(find_jump sub cond_unsat) ~data:true
    |> Pre.jmp_spec_reach
  in
  let env = Pre.mk_env ctx var_gen  ~jmp_spec ~subs:(Seq.singleton sub) in
  let post = true_constr ctx in
  let pre, _ = Pre.visit_sub env post sub in
  let solver = Z3.Solver.mk_simple_solver ctx in
  let result = Pre.check ~refute:false solver ctx pre in
  assert_equal ~ctxt:test_ctx ~printer:Z3.Solver.string_of_status
    Z3.Solver.UNSATISFIABLE result


let test_exclude_1 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let solver = Z3.Solver.mk_simple_solver ctx in
  let var = BV.mk_const_s ctx "x" 32 in
  let value = BV.mk_numeral ctx "0" 32 in
  let pre = Bool.mk_eq ctx var value
            |> Constr.mk_goal "x = 0"
            |> Constr.mk_constr
  in
  assert_equal ~ctxt:test_ctx ~printer:Z3.Solver.string_of_status
    Z3.Solver.SATISFIABLE (Pre.check solver ctx pre);
  assert_equal ~ctxt:test_ctx ~printer:Z3.Solver.string_of_status
    Z3.Solver.SATISFIABLE (Pre.exclude solver ctx ~var:var ~pre:pre);
  let model = Constr.get_model_exn solver in
  let regs = model
             |> Z3.Model.get_decls
             |> List.map ~f:(fun v -> Z3.FuncDecl.apply v [])
             |> List.map ~f:(Constr.eval_model_exn model)
  in
  List.iter regs ~f:(fun v ->
      assert_bool "Variable's value was not properly excluded from the model"
        (not (Expr.equal v value)))


let test_get_vars_1 (test_ctx : test_ctxt) : unit =
  let rdi = Var.create "RDI" reg64_t in
  let rsi = Var.create "RSI" reg64_t in
  let rdx = Var.create "RDX" reg64_t in
  let rcx = Var.create "RCX" reg64_t in
  let r8 = Var.create "R8" reg64_t in
  let r9 = Var.create "R9" reg64_t in
  let x = Var.create "x" reg64_t in
  let sub = Bil.(
      [
        x := i64 1;
      ]
    ) |> bil_to_sub
  in
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env = Pre.mk_env ctx var_gen ~use_fun_input_regs:true in
  let vars = Pre.get_vars env sub in
  assert_equal ~ctxt:test_ctx ~cmp:Var.Set.equal
    ~printer:(fun v -> v |> Var.Set.to_list |> List.to_string ~f:Var.to_string)
    (Var.Set.of_list [rdi; rsi; rdx; rcx; r8; r9; x]) vars


let test_get_vars_2 (test_ctx : test_ctxt) : unit =
  let x = Var.create "x" reg64_t in
  let sub = Bil.(
      [
        x := i64 1;
      ]
    ) |> bil_to_sub
  in
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env = Pre.mk_env ctx var_gen ~use_fun_input_regs:false in
  let vars = Pre.get_vars env sub in
  assert_equal ~ctxt:test_ctx ~cmp:Var.Set.equal
    ~printer:(fun v -> v |> Var.Set.to_list |> List.to_string ~f:Var.to_string)
    (Var.Set.of_list [x]) vars


let test_get_vars_inline_1 (test_ctx : test_ctxt) : unit =
  let x = Var.create "x" reg64_t in
  let y = Var.create "y" reg64_t in
  let loc = Var.create "loc" reg64_t in
  let mem = Var.create "mem" (mem64_t `r64) in
  let call_sub = Bil.(
      [
        mem := (store ~mem:(var mem) ~addr:(var loc) (var x) LittleEndian `r64)
      ]
    ) |> bil_to_sub in
  let sub = Bil.(
      [
        y := i64 2;
        jmp (unknown (call_sub |> Term.tid |> Tid.to_string) reg64_t)
      ]
    ) |> bil_to_sub
  in
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env = Pre.mk_env ctx var_gen ~use_fun_input_regs:false
      ~to_inline:(Seq.singleton call_sub) ~subs:(Seq.of_list [sub; call_sub]) in
  let vars = Pre.get_vars env sub in
  assert_equal ~ctxt:test_ctx ~cmp:Var.Set.equal
    ~printer:(fun v -> v |> Var.Set.to_list |> List.to_string ~f:Var.to_string)
    (Var.Set.of_list [x; y; loc; mem]) vars


let test_output_vars_1 (test_ctx : test_ctxt) : unit =
  let x = Var.create "x" reg32_t in
  let y = Var.create "y" reg32_t in
  let z = Var.create "z" reg32_t in
  let sub = Bil.(
      [
        x := i32 1;
        y := i32 2;
        z := i32 3;
      ]
    ) |> bil_to_sub
  in
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env = Pre.mk_env ctx var_gen in
  let vars = Pre.get_output_vars env sub ["x"; "y"; "z"] in
  assert_equal ~ctxt:test_ctx ~cmp:Var.Set.equal
    ~printer:(fun v -> v |> Var.Set.to_list |> List.to_string ~f:Var.to_string)
    (Var.Set.of_list [x; y; z]) vars


let test_output_vars_2 (test_ctx : test_ctxt) : unit =
  let x = Var.create "x" reg32_t in
  let y = Var.create "y" reg32_t in
  let sub = Bil.(
      [
        x := i32 1;
        y := i32 2;
      ]
    ) |> bil_to_sub
  in
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env = Pre.mk_env ctx var_gen in
  let vars = Pre.get_output_vars env sub ["x"; "y"; "z"] in
  assert_equal ~ctxt:test_ctx ~cmp:Var.Set.equal
    ~printer:(fun v -> v |> Var.Set.to_list |> List.to_string ~f:Var.to_string)
    (Var.Set.of_list [x; y]) vars


(* x := x + 1
   Post: x == init_x + 1 *)
let test_init_vars_1 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let x = Var.create "x" reg32_t in
  let sub = Bil.([ x := var x + i32 1; ]) |> bil_to_sub in
  let env = Pre.mk_env ctx var_gen ~subs:(Seq.singleton sub) in
  let z3_x, env = Env.get_var env x in
  let init_x, env = Env.mk_init_var env x in
  let post =
    Bool.mk_eq ctx z3_x (BV.mk_add ctx init_x (BV.mk_numeral ctx "1" 32))
    |> Constr.mk_goal "x == init_x + 1"
    |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_sub env post sub in
  let hyp =
    Bool.mk_eq ctx z3_x init_x
    |> Constr.mk_goal "x == init_x"
    |> Constr.mk_constr
  in
  let goal = Constr.mk_clause [hyp] [pre] in
  assert_z3_result test_ctx env (Sub.to_string sub) post goal Z3.Solver.UNSATISFIABLE


(* x := x + 1
   Post: x == init_x + 2 *)
let test_init_vars_2 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let x = Var.create "x" reg32_t in
  let sub = Bil.([ x := var x + i32 1; ]) |> bil_to_sub in
  let env = Pre.mk_env ctx var_gen ~subs:(Seq.singleton sub) in
  let z3_x, env = Env.get_var env x in
  let init_x, env = Env.mk_init_var env x in
  let post =
    Bool.mk_eq ctx z3_x (BV.mk_add ctx init_x (BV.mk_numeral ctx "2" 32))
    |> Constr.mk_goal "x == init_x + 2"
    |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_sub env post sub in
  let hyp =
    Bool.mk_eq ctx z3_x init_x
    |> Constr.mk_goal "x == init_x"
    |> Constr.mk_constr
  in
  let goal = Constr.mk_clause [hyp] [pre] in
  assert_z3_result test_ctx env (Sub.to_string sub) post goal Z3.Solver.SATISFIABLE


let suite = [
  "Empty Block" >:: test_empty_block;
  "Assign SSA block: y = x+1; Post: y == x+1" >:: test_assign_1;
  "Assign SSA block: y = x+1; Post: y == x" >:: test_assign_2;
  "Assign SSA block: y = x; x = x+1; Post: y == x-1" >:: test_assign_3;
  "Read/Write Little Endian: m = m[addr, el] <- x; y = m[addr, el]; Post: y == x" >:: test_read_write_1;
  "Read/Write Big Endian: m = m[addr, el] <- x; y = m[addr, el]; Post: y == x" >:: test_read_write_2;
  "Read/Write Mismatched Endian: m = m[addr, el] <- x; y = m[addr, el]; Post: y == x" >:: test_read_write_3;
  "Read/Write Mismatched Endian: m = m[addr, el] <- x; y = m[addr, el]; Post: y == x" >:: test_read_write_4;
  "Bit Shifting Logical: y = x; y = y << 2; y = y >> 2; Post: x == y" >:: test_bit_shift_1;
  "Bit Shifting Logical Overflow: y = x; y = y << 2; y = y >> 2; Post: x == y" >:: test_bit_shift_2;
  "Bit Shifting Arithmetic: y = x; y = y << 2; y = y ~>> 2; Post: x == y" >:: test_bit_ashift_1;
  "Bit Shifting Arithmetic Overflow: y = x; y = y << 2; y = y ~>> 2; Post: x == y" >:: test_bit_ashift_2;
  "Ite Assign: y = if x < 0x40 then x << 2 ~>> 2 else x" >:: test_ite_assign_1;

  "Subroutine: \n\
   bl: when x < 0xA goto b2; goto b3; \n\
   b2: y = x+1; goto b4; \n\
   b3: y = x-1; goto b4; \n\
   b4: z = y;" >:: test_subroutine_1;
  "Subroutine: \n\
   bl: when x < 0xA goto b2; goto b3; \n\
   b2: y = x+1; goto b4; \n\
   b3: y = x-1; goto b4; \n\
   b4: z = y; \n \
   but using the smt-lib parser for the postcondition" >:: test_subroutine_1_2;
  "Ends with two blocks: \n\
   b1: when x < 0 goto b2; goto b3; \n\
   b2: x = y; \n\
   b3: x = z;" >:: test_subroutine_3;
  "Starts with two blocks: \n\
   b1: x = y; goto b3; \n\
   b2: x = z; goto b3; \n\
   b3: w = x;" >:: test_subroutine_4;
  "Call function: \n\
   b1: x = y; call b4 with return b2; \n\
   b2: x = x + 1; goto b3 \n\
   b3: z = x; \n\
   b4: noop;" >:: test_subroutine_5;
  "Assert fail label: \n\
   b1: call @__assert_fail with return b2; \n\
   b2: noop;" >:: test_subroutine_6;
  "Assert fail BIL: \n\
   b1: call @__assert_fail with no return; \
  " >:: test_subroutine_7;
  "Assert loc <> 0:\n\
   if mem[loc] = 12 then else; \
   //using the \"assume non-null\" generator" >:: test_subroutine_8;
  "Call fail: \n\
  " >:: test_call_1;
  "Call vars with spec_arg_terms: \n\
  " >:: test_call_2;
  "Call vars with spec_rax_out: \n\
  " >:: test_call_3;
  "Call vars with spec_default: \n\
  " >:: test_call_4;
  "Call vars: fun not called: \n\
  " >:: test_call_5;
  "Call vars with branches: \n\
  " >:: test_call_6;
  "Test call with function inlining UNSAT: \n\
  " >:: test_call_7;
  "Test call with disabling function inlining SAT: \n\
  " >:: test_call_8;
  "Test call with nested function inlining UNSAT: \n\
  " >:: test_call_9;
  "Test call with nested function inlining SAT (don't inline everything): \n\
  " >:: test_call_10;
  "Interrupt 0x0: \n\
  " >:: test_int_1;
  "Loop: \n\
   b1: x = a; y = b; goto b2; \n\
   b2: x = x + 1; y = y - 1; when y <= 0 goto b3; goto b2; \n\
   b3:" >:: test_loop_1;
  "Loop: \n\
   b1: x = 0; y = 5; goto b2; \n\
   b2: x = x + 1; y = y - 1; when y <= 0 goto b3; goto b2; \n\
   b3:" >:: test_loop_2;
  "Loop: \n\
   b1: x = 0; y = 6; goto b2; \n\
   b2: x = x + 1; y = y - 1; when y <= 0 goto b3; goto b2; \n\
   b3:" >:: test_loop_3;
  "Loop: \n\
   b1: x = 0; y = 2; goto b2; \n\
   b2: x = x + 1; y = y - 1; when y <= 0 goto b3; goto b2; \n\
   b3:" >:: test_loop_4;
  "Loop: \n\
   b1: x = 0; y = 1; goto b2; \n\
   b2: x = x + 1; y = y - 1; when y <= 0 goto b3; goto b2; \n\
   b3: x = x + 2;" >:: test_loop_5;
  "Loop: \n\
   b1: x = 0; y = 5; goto b2; \n\
   b2: x = x + 1; y = y - 1; when y > 0 goto b2; goto b3; \n\
   b3: x = x + 2" >:: test_loop_6;
  "Read NULL; SAT:\n\
   x = mem[addr];" >:: test_exp_cond_1;
  "Read NULL; UNSAT:\n\
   addr = 0x40000000;\
   x = mem[addr];" >:: test_exp_cond_2;

  "Signed: Bitwidth 3 -> 8; Value 6 -> -2" >:: test_cast 3 8 6 Bil.SIGNED;
  "Unsigned: Bitwidth 3 -> 8; Value 6 -> 6" >:: test_cast 3 8 6 Bil.UNSIGNED;
  "High: Bitwidth 8 -> 5; Value: 238 -> 29" >:: test_cast 8 5 238 Bil.HIGH;
  "Low: Bitwidth 8 -> 5; Value: 238 -> 14" >:: test_cast 8 5 238 Bil.LOW;

  "Test Shift Bitwidth" >:: test_shift_bitwidth;

  "Test branches" >:: test_branches_1;
  "Test jmp_spec_reach SAT" >:: test_jmp_spec_reach_1;
  "Test jmp_spec_reach UNSAT" >:: test_jmp_spec_reach_2;

  "Test exclude" >:: test_exclude_1;

  "Use fun input registers in get_vars" >:: test_get_vars_1;
  "Don't use fun input registers in get_vars" >:: test_get_vars_2;
  "Collect vars from inlined functions" >:: test_get_vars_inline_1;

  "Test get output variables by name" >:: test_output_vars_1;
  "z not in subroutine" >:: test_output_vars_2;

  "Compare init and current vals of var: UNSAT" >:: test_init_vars_1;
  "Compare init and current vals of var: SAT" >:: test_init_vars_2;
]
