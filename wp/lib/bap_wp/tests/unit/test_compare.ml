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
module Comp = Compare
module Constr = Constraint
module Env = Environment
module Bool = Z3.Boolean
module BV = Z3.BitVector

(* To run these tests: `make test.unit` in bap_wp directory *)

let assert_z3_compare (test_ctx : test_ctxt) (body1 : string) (body2 : string)
    (pre : Constr.t) (expected : Z3.Solver.status) ~orig:(env1 : Env.t)
    ~modif:(env2 : Env.t) : unit =
  let z3_ctx = Env.get_context env1 in
  let solver = Z3.Solver.mk_simple_solver z3_ctx in
  let result = Pre.check solver z3_ctx pre in
  let pp_constr = Constr.pp_constr ~colorful:false in 
  assert_equal ~ctxt:test_ctx
    ~printer:Z3.Solver.string_of_status
    ~pp_diff:(fun ff (exp, real) ->
        Format.fprintf ff "\n\nComparing:\n%s\nand\n\n%s\nCompare_prop:\n%a\n\n%!"
          body1 body2 pp_constr pre;
        print_z3_model solver exp real pre ~orig:env1 ~modif:env2)
    expected result


let test_block_pair_1 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env1 = Pre.mk_env ctx var_gen in
  let env2 = Pre.mk_env ctx var_gen in
  let x = Var.create "x" reg32_t in
  let y = Var.create "y" reg32_t in
  let z = Var.create "z" reg32_t in
  let blk1 = Blk.create () |> mk_def z (Bil.binop Bil.plus (Bil.var x) (Bil.var y)) in
  let blk2 = Blk.create ()
             |> mk_def x (Bil.binop Bil.plus (Bil.var x) one)
             |> mk_def y (Bil.binop Bil.minus (Bil.var y) one)
             |> mk_def z (Bil.binop Bil.plus (Bil.var x) (Bil.var y))
  in
  let pre_regs = Var.Set.union (Var.Set.singleton x) (Var.Set.singleton y) in
  let post_regs = Var.Set.singleton z in
  let compare_prop, env1, env2 = Comp.compare_blocks
      ~pre_regs ~post_regs
      ~original:(blk1,env1) ~modified:(blk2,env2)
      ~smtlib_post:"" ~smtlib_hyp:"" in
  assert_z3_compare test_ctx ~orig:env1 ~modif:env2
    (Blk.to_string blk1) (Blk.to_string blk2)
    compare_prop Z3.Solver.UNSATISFIABLE


let test_block_pair_2 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env1 = Pre.mk_env ctx var_gen in
  let env2 = Pre.mk_env ctx var_gen in
  let x = Var.create "x" reg32_t in
  let y = Var.create "y" reg32_t in
  let z = Var.create "z" reg32_t in
  let blk1 = Blk.create () |> mk_def z (Bil.var x) in
  let blk2 = Blk.create ()
             |> mk_def y (Bil.var x)
             |> mk_def z (Bil.var y)
  in
  let pre_regs = Var.Set.singleton x in
  let post_regs = Var.Set.singleton z in
  let compare_prop, env1, env2 = Comp.compare_blocks
      ~pre_regs ~post_regs
      ~original:(blk1,env1) ~modified:(blk2,env2)
      ~smtlib_post:"" ~smtlib_hyp:"" in
  assert_z3_compare test_ctx ~orig:env1 ~modif:env2
    (Blk.to_string blk1) (Blk.to_string blk2)
    compare_prop Z3.Solver.UNSATISFIABLE


let test_sub_pair_1 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env1 = Pre.mk_env ctx var_gen in
  let env2 = Pre.mk_env ctx var_gen in
  let def_y_tid = Tid.create () in
  let blk1 = Blk.create () in
  let blk2 = Blk.create () in
  let blk3 = Blk.create () in
  let blk4 = Blk.create () in
  let x = Var.create "x" reg32_t in
  let y = Var.create "y" reg32_t in
  let z = Var.create "z" reg32_t in
  let lt = Bil.( (var x) < (i32 0) ) in
  let blk1 = blk1 |> mk_cond lt blk2 blk3 in
  let blk2 = blk2
             |> mk_def ~tid:def_y_tid y one
             |> mk_jmp blk4
  in
  let blk3 = blk3
             |> mk_def ~tid:def_y_tid y two
             |> mk_jmp blk4
  in
  let blk4 = blk4
             |> mk_def y (Bil.var x)
             |> mk_def z (Bil.var y)
  in
  let sub1 = mk_sub [blk1; blk2; blk3; blk4] in
  let blk2' = Term.remove def_t blk2 def_y_tid in
  let blk3' = Term.remove def_t blk3 def_y_tid in
  let sub2 = mk_sub [blk1; blk2'; blk3'; blk4] in
  let pre_regs = Var.Set.union (Var.Set.singleton x) (Var.Set.singleton y) in
  let post_regs = Var.Set.singleton z in
  let post, hyps = Comp.compare_subs_eq ~pre_regs ~post_regs in
  let compare_prop, env1, env2 = Comp.compare_subs
      ~postconds:[post] ~hyps:[hyps]
      ~original:(sub1, env1) ~modified:(sub2, env2)
  in
  assert_z3_compare test_ctx ~orig:env1 ~modif:env2
    (Sub.to_string sub1) (Sub.to_string sub2)
    compare_prop Z3.Solver.UNSATISFIABLE


let test_sub_pair_2 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env1 = Pre.mk_env ctx var_gen in
  let env2 = Pre.mk_env ctx var_gen in
  let def_y_tid = Tid.create () in
  let blk1 = Blk.create () in
  let blk2 = Blk.create () in
  let blk3 = Blk.create () in
  let blk4 = Blk.create () in
  let x = Var.create "x" reg32_t in
  let y = Var.create "y" reg32_t in
  let z = Var.create "z" reg32_t in
  let lt = Bil.( (var x) < (i32 1) ) in
  let blk1 = blk1 |> mk_cond lt blk2 blk3 in
  let blk2 = blk2
             |> mk_def y one
             |> mk_jmp blk4
  in
  let blk3 = blk3
             |> mk_def y two
             |> mk_jmp blk4
  in
  let blk4 = blk4
             |> mk_def ~tid:def_y_tid y (Bil.var x)
             |> mk_def z (Bil.var y)
  in
  let sub1 = mk_sub [blk1; blk2; blk3; blk4] in
  let blk4' = Term.remove def_t blk4 def_y_tid in
  let sub2 = mk_sub [blk1; blk2; blk3; blk4'] in
  let pre_regs = Var.Set.union (Var.Set.singleton x) (Var.Set.singleton y) in
  let post_regs = Var.Set.singleton z in
  let post, hyps = Comp.compare_subs_eq ~pre_regs ~post_regs in
  let compare_prop, env1, env2 = Comp.compare_subs
      ~postconds:[post] ~hyps:[hyps]
      ~original:(sub1, env1) ~modified:(sub2, env2)
  in
  assert_z3_compare test_ctx ~orig:env1 ~modif:env2
    (Sub.to_string sub1) (Sub.to_string sub2)
    compare_prop Z3.Solver.SATISFIABLE


let test_sub_pair_3 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env1 = Pre.mk_env ctx var_gen in
  let env2 = Pre.mk_env ctx var_gen in
  let blk1 = Blk.create () in
  let blk2 = Blk.create () in
  let blk1' = Blk.create () in
  let blk2' = Blk.create () in
  let x = Var.create "x" reg32_t in
  let y = Var.create "y" reg32_t in
  let z = Var.create "z" reg32_t in
  let blk1 = blk1
             |> mk_def x Bil.( (var y) + (i32 2) )
             |> mk_jmp blk2
  in
  let blk2 = blk2 |> mk_def z (Bil.var x) in
  let blk1' = blk1'
              |> mk_def z Bil.( (var y) + (i32 1) )
              |> mk_jmp blk2'
  in
  let blk2' = blk2' |> mk_def z Bil.( (var z) + (i32 1) ) in
  let sub1 = mk_sub [blk1; blk2] in
  let sub2 = mk_sub [blk1'; blk2'] in
  let pre_regs = Var.Set.union (Var.Set.singleton x) (Var.Set.singleton y) in
  let post_regs = Var.Set.singleton z in
  let post, hyps = Comp.compare_subs_eq ~pre_regs ~post_regs in
  let compare_prop, env1, env2 = Comp.compare_subs
      ~postconds:[post] ~hyps:[hyps]
      ~original:(sub1, env1) ~modified:(sub2, env2)
  in
  assert_z3_compare test_ctx ~orig:env1 ~modif:env2
    (Sub.to_string sub1) (Sub.to_string sub2)
    compare_prop Z3.Solver.UNSATISFIABLE


let test_sub_pair_4 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env1 = Pre.mk_env ctx var_gen in
  let env2 = Pre.mk_env ctx var_gen in
  let x = Var.create "x" reg32_t in
  let y = Var.create "y" reg32_t in
  let sub1 = Bil.(
      [ if_ ( var x < (int @@ Word.of_int 0x40000000 ~width:32) )
          [
            y := var x;
            y := (var y) lsl two;
            y := (var y) lsr two
          ]
          [
            y := var x
          ]
      ]
    ) |> bil_to_sub
  in
  let sub2 = Bil.(
      [
        y := ite ~if_:( var x < (int @@ Word.of_int 0x40000000 ~width:32) )
            ~then_:( (var x lsl two) lsr two) ~else_:(var x)
      ]
    ) |> bil_to_sub
  in
  let pre_regs = Var.Set.singleton x in
  let post_regs = Var.Set.singleton y in
  let post, hyps = Comp.compare_subs_eq ~pre_regs ~post_regs in
  let compare_prop, env1, env2 = Comp.compare_subs
      ~postconds:[post] ~hyps:[hyps]
      ~original:(sub1, env1) ~modified:(sub2, env2)
  in
  assert_z3_compare test_ctx ~orig:env1 ~modif:env2
    (Sub.to_string sub1) (Sub.to_string sub2)
    compare_prop Z3.Solver.UNSATISFIABLE


let test_sub_pair_5 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env1 = Pre.mk_env ctx var_gen in
  let env2 = Pre.mk_env ctx var_gen in
  let blk1 = Blk.create () in
  let blk2 = Blk.create () in
  let blk3 = Blk.create () in
  let blk1' = Blk.create () in
  let x = Var.create "x" reg32_t in
  let y = Var.create "y" reg32_t in
  let lt = Bil.binop Bil.lt (Bil.var x) (Bil.int @@ Word.of_int 0x40000000 ~width:32) in
  let lshift = Bil.binop Bil.lshift (Bil.var y) two in
  let rshift = Bil.binop Bil.rshift (Bil.var y) two in
  let lshift' = Bil.binop Bil.lshift (Bil.var x) two in
  let rshift' = Bil.binop Bil.rshift (lshift') two in
  let ite = Bil.ite ~if_:lt ~then_:rshift' ~else_:(Bil.var x) in
  let blk1 = blk1 |> mk_cond lt blk2 blk3 in
  let blk2 = blk2 |> mk_def y (Bil.var x) in
  let blk3 = blk3
             |> mk_def y (Bil.var x)
             |> mk_def y lshift
             |> mk_def y rshift
  in
  let blk1' = blk1' |> mk_def y ite in
  let sub1 = mk_sub [blk1; blk2; blk3] in
  let sub2 = mk_sub [blk1'] in
  let pre_regs = Var.Set.singleton x in
  let post_regs = Var.Set.singleton y in
  let post, hyps = Comp.compare_subs_eq ~pre_regs ~post_regs in
  let compare_prop, env1, env2 = Comp.compare_subs
      ~postconds:[post] ~hyps:[hyps]
      ~original:(sub1, env1) ~modified:(sub2, env2)
  in
  assert_z3_compare test_ctx ~orig:env1 ~modif:env2
    (Sub.to_string sub1) (Sub.to_string sub2)
    compare_prop Z3.Solver.SATISFIABLE


let test_sub_pair_6 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env1 = Pre.mk_env ctx var_gen ~arch:`x86 ~exp_conds:[Pre.non_null_load_assert] in
  let env2 = Pre.mk_env ctx var_gen ~arch:`x86 ~exp_conds:[Pre.non_null_load_vc] in
  let mem = Var.create "mem" (mem32_t `r32) in
  let loc = Var.create "loc" reg32_t in
  let read = Bil.(load ~mem:(var mem) ~addr:(var loc) LittleEndian `r32) in
  let sub1 = Bil.([if_ (read = i32 12)[][]]) |> bil_to_sub in
  let sub2 = Bil.([if_ (read = i32 3) [if_ (read = i32 4) [][]] []]) |> bil_to_sub in
  let post, hyps = Comp.compare_subs_empty_post in
  let compare_prop, env1, env2 = Comp.compare_subs
      ~postconds:[post] ~hyps:[hyps]
      ~original:(sub1, env1) ~modified:(sub2, env2)
  in
  assert_z3_compare test_ctx ~orig:env1 ~modif:env2
    (Sub.to_string sub1) (Sub.to_string sub2)
    compare_prop Z3.Solver.UNSATISFIABLE


let test_sub_pair_7 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env1 = Pre.mk_env ctx var_gen ~arch:`x86 ~exp_conds:[Pre.non_null_load_assert] in
  let env2 = Pre.mk_env ctx var_gen ~arch:`x86 ~exp_conds:[Pre.non_null_load_vc] in
  let mem = Var.create "mem" (mem32_t `r32) in
  let loc = Var.create "loc" reg32_t in
  let read = Bil.(load ~mem:(var mem) ~addr:(var loc) LittleEndian `r32) in
  let read' = Bil.(load ~mem:(var mem) ~addr:(var loc + one) LittleEndian `r32) in
  let sub1 = Bil.([if_ (read = i32 3)[][]]) |> bil_to_sub in
  let sub2 = Bil.([if_ (read = i32 3) [if_ (read' = i32 4) [][]] []]) |> bil_to_sub in
  let post, hyps = Comp.compare_subs_empty_post in
  let compare_prop, env1, env2 = Comp.compare_subs
      ~postconds:[post] ~hyps:[hyps]
      ~original:(sub1, env1) ~modified:(sub2, env2)
  in
  assert_z3_compare test_ctx ~orig:env1 ~modif:env2
    (Sub.to_string sub1) (Sub.to_string sub2)
    compare_prop Z3.Solver.SATISFIABLE


let test_sub_pair_fun_1 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let call_tid = Tid.create () in
  Tid.set_name call_tid "call_tid";
  let sub1_tid = Tid.create () in
  let sub2_tid = Tid.create () in
  let blk1 = Blk.create () in
  let blk2 = Blk.create () in
  let blk3 = Blk.create () in
  let blk4 = Blk.create () in
  let call_blk = Blk.create () in
  let call_sub = mk_sub ~tid:call_tid ~name:"test_call" [call_blk] in
  let blk1 = blk1 |> mk_call (Label.direct (Term.tid blk2)) (Label.direct (Term.tid call_sub)) in
  let blk3 = blk3 |> mk_call (Label.direct (Term.tid blk4)) (Label.direct (Term.tid call_sub)) in
  let main_sub1 = mk_sub ~tid:sub1_tid ~name:"main_sub" [blk1; blk2] in
  let main_sub2 = mk_sub ~tid:sub2_tid ~name:"main_sub" [blk3; blk4] in
  let env1 = Pre.mk_env ctx var_gen ~subs:(Seq.of_list [main_sub1; call_sub]) in
  let env2 = Pre.mk_env ctx var_gen ~subs:(Seq.of_list [main_sub2; call_sub]) in
  let post, hyps = Comp.compare_subs_fun in
  let compare_prop, env1, env2 = Comp.compare_subs
      ~postconds:[post] ~hyps:[hyps]
      ~original:(main_sub1, env1) ~modified:(main_sub2, env2)
  in
  assert_z3_compare test_ctx ~orig:env1 ~modif:env2
    (Sub.to_string main_sub1) (Sub.to_string main_sub2)
    compare_prop Z3.Solver.UNSATISFIABLE


let test_sub_pair_fun_2 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let call_tid = Tid.create () in
  Tid.set_name call_tid "call_tid";
  let sub1_tid = Tid.create () in
  let sub2_tid = Tid.create () in
  let blk1 = Blk.create () in
  let blk2 = Blk.create () in
  let blk3 = Blk.create () in
  let blk4 = Blk.create () in
  let call_blk = Blk.create () in
  let call_sub = mk_sub ~tid:call_tid ~name:"test_call" [call_blk] in
  let blk3 = blk3 |> mk_call (Label.direct (Term.tid blk4)) (Label.direct (Term.tid call_sub)) in
  let main_sub1 = mk_sub ~tid:sub1_tid ~name:"main_sub" [blk1; blk2] in
  let main_sub2 = mk_sub ~tid:sub2_tid ~name:"main_sub" [blk3; blk4] in
  let env1 = Pre.mk_env ctx var_gen ~subs:(Seq.of_list [main_sub1; call_sub]) in
  let env2 = Pre.mk_env ctx var_gen ~subs:(Seq.of_list [main_sub2; call_sub]) in
  let post, hyps = Comp.compare_subs_fun in
  let compare_prop, env1, env2 = Comp.compare_subs
      ~postconds:[post] ~hyps:[hyps]
      ~original:(main_sub1, env1) ~modified:(main_sub2, env2)
  in
  assert_z3_compare test_ctx ~orig:env1 ~modif:env2
    (Sub.to_string main_sub1) (Sub.to_string main_sub2)
    compare_prop Z3.Solver.SATISFIABLE


let test_sub_pair_fun_3 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let call1_tid = Tid.create () in
  Tid.set_name call1_tid "call1_tid";
  let call2_tid = Tid.create () in
  Tid.set_name call2_tid "call2_tid";
  let sub1_tid = Tid.create () in
  let sub2_tid = Tid.create () in
  let blk1 = Blk.create () in
  let blk2 = Blk.create () in
  let blk3 = Blk.create () in
  let blk4 = Blk.create () in
  let blk1' = Blk.create () in
  let call_blk = Blk.create () in
  let call1_sub = mk_sub ~tid:call1_tid ~name:"test_call1" [call_blk] in
  let call2_sub = mk_sub ~tid:call2_tid ~name:"test_call2" [call_blk] in
  let x = Var.create "x" reg32_t in
  let cond = Bil.binop Bil.le (Bil.var x) zero in
  let cond' = Bil.binop Bil.le (Bil.var x) one in
  let blk1 = blk1 |> mk_cond cond blk2 blk3 in
  let blk1' = blk1' |> mk_cond cond' blk2 blk3 in
  let blk2 = blk2 |> mk_call (Label.direct (Term.tid blk4)) (Label.direct (Term.tid call1_sub)) in
  let blk3 = blk3 |> mk_call (Label.direct (Term.tid blk4)) (Label.direct (Term.tid call2_sub)) in
  let main_sub1 = mk_sub ~tid:sub1_tid ~name:"main_sub" [blk1; blk2; blk3; blk4] in
  let main_sub2 = mk_sub ~tid:sub2_tid ~name:"main_sub" [blk1'; blk2; blk3; blk4] in
  let env1 = Pre.mk_env ctx var_gen
      ~subs:(Seq.of_list [main_sub1; call1_sub; call2_sub]) in
  let env2 = Pre.mk_env ctx var_gen
      ~subs:(Seq.of_list [main_sub2; call1_sub; call2_sub]) in
  let post, hyps = Comp.compare_subs_fun in
  let compare_prop, env1, env2 = Comp.compare_subs
      ~postconds:[post] ~hyps:[hyps]
      ~original:(main_sub1, env1) ~modified:(main_sub2, env2)
  in
  assert_z3_compare test_ctx ~orig:env1 ~modif:env2
    (Sub.to_string main_sub1) (Sub.to_string main_sub2)
    compare_prop Z3.Solver.SATISFIABLE


let test_sub_pair_fun_4 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let call1_tid = Tid.create () in
  Tid.set_name call1_tid "call1_tid";
  let call2_tid = Tid.create () in
  Tid.set_name call2_tid "call2_tid";
  let sub1_tid = Tid.create () in
  let sub2_tid = Tid.create () in
  let blk1 = Blk.create () in
  let blk2 = Blk.create () in
  let blk3 = Blk.create () in
  let blk4 = Blk.create () in
  let blk1' = Blk.create () in
  let blk2' = Blk.create () in
  let call_blk = Blk.create () in
  let call1_sub = mk_sub ~tid:call1_tid ~name:"test_call1" [call_blk] in
  let call2_sub = mk_sub ~tid:call2_tid ~name:"test_call2" [call_blk] in
  let x = Var.create "x" reg32_t in
  let cond = Bil.binop Bil.le (Bil.var x) zero in
  let blk1 = blk1 |> mk_cond cond blk2 blk3 in
  let blk2 = blk2 |> mk_call (Label.direct (Term.tid blk4)) (Label.direct (Term.tid call1_sub)) in
  let blk3 = blk3 |> mk_call (Label.direct (Term.tid blk4)) (Label.direct (Term.tid call2_sub)) in
  let blk1' = blk1' |> mk_call (Label.direct (Term.tid blk2')) (Label.direct (Term.tid call1_sub)) in
  let blk2' = blk2' |> mk_call (Label.direct (Term.tid blk4)) (Label.direct (Term.tid call2_sub)) in
  let main_sub1 = mk_sub ~tid:sub1_tid ~name:"main_sub" [blk1; blk2; blk3; blk4] in
  let main_sub2 = mk_sub ~tid:sub2_tid ~name:"main_sub" [blk1'; blk2'; blk4] in
  let env1 = Pre.mk_env ctx var_gen
      ~subs:(Seq.of_list [main_sub1; call1_sub; call2_sub]) in
  let env2 = Pre.mk_env ctx var_gen
      ~subs:(Seq.of_list [main_sub2; call1_sub; call2_sub]) in
  let post, hyps = Comp.compare_subs_fun in
  let compare_prop, env1, env2 = Comp.compare_subs
      ~postconds:[post] ~hyps:[hyps]
      ~original:(main_sub1, env1) ~modified:(main_sub2, env2)
  in
  assert_z3_compare test_ctx ~orig:env1 ~modif:env2
    (Sub.to_string main_sub1) (Sub.to_string main_sub2)
    compare_prop Z3.Solver.SATISFIABLE


let test_fun_outputs_1 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let ret_var = Var.create "RAX" reg64_t in
  let rdi = Var.create "RDI" reg64_t in
  let rsi = Var.create "RSI" reg64_t in
  let sub1 = Bil.([ ret_var := var rdi + var rsi ]) |> bil_to_sub in
  let sub2 = Bil.([ ret_var := var rdi + var rsi ]) |> bil_to_sub in
  let sub1 = Sub.with_name sub1 "test_call" in
  let sub2 = Sub.with_name sub2 "test_call" in
  let main_sub1 =
    [call sub1 reg64_t]
    |> bil_to_sub in
  let main_sub2 =
    [call sub2 reg64_t]
    |> bil_to_sub in
  let env1 = Pre.mk_env ctx var_gen ~subs:(Seq.of_list [main_sub1; sub1])
      ~specs:[Pre.spec_chaos_caller_saved] in
  let env2 = Pre.mk_env ctx var_gen ~subs:(Seq.of_list [main_sub2; sub2])
      ~specs:[Pre.spec_chaos_caller_saved] in
  let pre_regs = Var.Set.of_list (ret_var :: x86_64_input_regs) in
  let post_regs = Var.Set.singleton ret_var in
  let post, hyps = Comp.compare_subs_eq ~pre_regs ~post_regs in
  let compare_prop, env1, env2 = Comp.compare_subs
      ~postconds:[post] ~hyps:[hyps]
      ~original:(main_sub1, env1) ~modified:(main_sub2, env2)
  in
  assert_z3_compare test_ctx ~orig:env1 ~modif:env2
    (Sub.to_string main_sub1)
    (Sub.to_string main_sub2)
    compare_prop Z3.Solver.UNSATISFIABLE


let test_fun_outputs_2 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let ret_var = Var.create "RAX" reg64_t in
  let rdi = Var.create "RDI" reg64_t in
  let rsi = Var.create "RSI" reg64_t in
  let sub1 = Bil.([ ret_var := var rdi + var rsi ]) |> bil_to_sub in
  let sub2 = Bil.([ ret_var := var rdi + var rsi ]) |> bil_to_sub in
  let sub1 = Sub.with_name sub1 "test_call" in
  let sub2 = Sub.with_name sub2 "test_call" in
  let main_sub1 =
    Bil.([ rdi := i64 1 ;
           rsi := i64 2 ; 
           Bil_to_bir.call sub1 reg64_t]) |> bil_to_sub in
  let main_sub2 =
    Bil.([ rdi := i64 2 ;
           rsi := i64 3 ;
           Bil_to_bir.call sub2 reg64_t]) |> bil_to_sub in
  let env1 = Pre.mk_env ctx var_gen ~subs:(Seq.of_list [main_sub1; sub1])
      ~specs:[Pre.spec_chaos_caller_saved] in
  let env2 = Pre.mk_env ctx var_gen ~subs:(Seq.of_list [main_sub2; sub2])
      ~specs:[Pre.spec_chaos_caller_saved] in
  let pre_regs = Var.Set.of_list (ret_var :: x86_64_input_regs) in
  let post_regs = Var.Set.singleton ret_var in
  let post, hyps = Comp.compare_subs_eq ~pre_regs ~post_regs in
  let compare_prop, env1, env2 = Comp.compare_subs
      ~postconds:[post] ~hyps:[hyps]
      ~original:(main_sub1, env1) ~modified:(main_sub2, env2)
  in
  assert_z3_compare test_ctx ~orig:env1 ~modif:env2
    (Sub.to_string main_sub1)
    (Sub.to_string main_sub2)
    compare_prop Z3.Solver.SATISFIABLE


let test_fun_outputs_3 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let rdi = Var.create "RDI" reg64_t in
  let rsi = Var.create "RSI" reg64_t in
  let rdx = Var.create "RDX" reg64_t in
  let rax = Var.create "RAX" reg64_t in
  let sub1 = Bil.([ rax := var rdi + var rsi ]) |> bil_to_sub in
  let sub2 = Bil.([ rax := var rdi + var rsi ]) |> bil_to_sub in
  let sub1 = Sub.with_name sub1 "test_call" in
  let sub2 = Sub.with_name sub2 "test_call" in
  let main_sub1 =
    Bil.([rdi := i64 1 ;
          rsi := i64 2 ;
          rdx := i64 3 ;
          Bil_to_bir.call sub1 reg64_t])
    |> bil_to_sub in
  let main_sub2 =
    Bil.([rdi := i64 1 ;
          rsi := i64 2 ;
          rdx := i64 4 ;
          Bil_to_bir.call sub2 reg64_t])
    |> bil_to_sub in
  let env1 = Pre.mk_env ctx var_gen ~specs:[Pre.spec_chaos_caller_saved]
      ~subs:(Seq.of_list [main_sub1; sub1]) in
  let env2 = Pre.mk_env ctx var_gen ~specs:[Pre.spec_chaos_caller_saved]
      ~subs:(Seq.of_list [main_sub2; sub2]) in
  let pre_regs = Var.Set.of_list (rax :: x86_64_input_regs) in
  let post_regs = Var.Set.singleton rax in
  let post, hyps = Comp.compare_subs_eq ~pre_regs ~post_regs in
  let compare_prop, env1, env2 = Comp.compare_subs
      ~postconds:[post] ~hyps:[hyps]
      ~original:(main_sub1, env1) ~modified:(main_sub2, env2)
  in
  assert_z3_compare test_ctx ~orig:env1 ~modif:env2
    (Sub.to_string main_sub1)
    (Sub.to_string main_sub2)
    compare_prop Z3.Solver.SATISFIABLE


let test_fun_outputs_4 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let rdi = Var.create "RDI" reg64_t in
  let rsi = Var.create "RSI" reg64_t in
  let rdx = Var.create "RDX" reg64_t in
  let rax = Var.create "RAX" reg64_t in
  let sub1 = Bil.([ rax := var rdi + var rsi ]) |> bil_to_sub in
  let sub2 = Bil.([ rax := var rdi + var rsi ]) |> bil_to_sub in
  let sub1 = Sub.with_name sub1 "test_call" in
  let sub2 = Sub.with_name sub2 "test_call" in
  let main_sub1 =
    Bil.([rdi := i64 1 ;
          rsi := i64 2 ;
          rdx := i64 3 ;
          Bil_to_bir.call sub1 reg64_t])
    |> bil_to_sub in
  let main_sub2 =
    Bil.([rdi := i64 1 ;
          rsi := i64 2 ;
          rdx := i64 4 ;
          Bil_to_bir.call sub2 reg64_t])
    |> bil_to_sub in
  let env1 = Pre.mk_env ctx var_gen ~specs:[Pre.spec_chaos_caller_saved]
      ~subs:(Seq.of_list [main_sub1; sub1]) ~use_fun_input_regs:false in
  let env2 = Pre.mk_env ctx var_gen ~specs:[Pre.spec_chaos_caller_saved]
      ~subs:(Seq.of_list [main_sub2; sub2]) ~use_fun_input_regs:false in
  let pre_regs = Var.Set.of_list (rax :: x86_64_input_regs) in
  let post_regs = Var.Set.singleton rax in
  let post, hyps = Comp.compare_subs_eq ~pre_regs ~post_regs in
  let compare_prop, env1, env2 = Comp.compare_subs
      ~postconds:[post] ~hyps:[hyps]
      ~original:(main_sub1, env1) ~modified:(main_sub2, env2)
  in
  assert_z3_compare test_ctx ~orig:env1 ~modif:env2
    (Sub.to_string main_sub1)
    (Sub.to_string main_sub2)
    compare_prop Z3.Solver.UNSATISFIABLE


let test_sub_pair_mem_1 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let blk1 = Blk.create () in
  let blk2 = Blk.create () in
  let mem = Var.create "mem" (mem32_t `r32) in
  let loc1 = Var.create "loc" reg32_t in
  let bv1 = Word.of_int ~width:32 0xDEADBEEF in
  let bv2 = Word.of_int ~width:32 0x0FA1AFE1 in
  let store1 = Bil.(store ~mem:(var mem) ~addr:(var loc1) (int bv1) LittleEndian `r32) in
  let store2 = Bil.(store ~mem:(var mem) ~addr:(var loc1) (int bv2) LittleEndian `r32) in
  let blk1 = blk1 |> mk_def mem store1 in
  let blk2 = blk2 |> mk_def mem store2 in
  let sub1 = mk_sub ~name:"main_sub" [blk1] in
  let sub2 = mk_sub ~name:"main_sub" [blk2] in
  let env1 = Pre.mk_env ctx var_gen ~subs:(Seq.of_list [sub1]) in
  let env2 = Pre.mk_env ctx var_gen ~subs:(Seq.of_list [sub2]) in
  let pre_regs = Var.Set.of_list [mem; loc1] in
  let post_regs = Var.Set.singleton mem in
  let post, hyps = Comp.compare_subs_eq ~pre_regs ~post_regs in
  let compare_prop, env1, env2 = Comp.compare_subs
      ~postconds:[post] ~hyps:[hyps]
      ~original:(sub1, env1) ~modified:(sub2, env2)
  in
  assert_z3_compare test_ctx ~orig:env1 ~modif:env2
    (Sub.to_string sub1) (Sub.to_string sub2)
    compare_prop Z3.Solver.SATISFIABLE


(* RAX := mem[0x600160, el]:u64
   vs
   RAX := mem[0x600161, el]:u64 *)
let test_memory_model_1 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let module Target = (val target_of_arch `x86_64) in
  let mem = Target.CPU.mem in
  let rax = Var.create "RAX" reg64_t in
  let addr1 = 0x600160 in
  let addr2 = 0x600161 in
  let sub1 = Bil.(
      [ rax := load ~mem:(var mem) ~addr:(i64 addr1) LittleEndian `r64; ]
    ) |> bil_to_sub in
  let sub2 = Bil.(
      [ rax := load ~mem:(var mem) ~addr:(i64 addr2) LittleEndian `r64; ]
    ) |> bil_to_sub in
  let offset = fun addr ->
    let width = addr |> Z3.Expr.get_sort |> Z3.BitVector.get_size in
    let offset = Z3.BitVector.mk_numeral ctx "1" width in
    Z3.BitVector.mk_add ctx addr offset
  in
  let pre_regs = Var.Set.of_list [rax; mem] in
  let post_regs = Var.Set.singleton rax in
  let env2 = Pre.mk_env ctx var_gen ~subs:(Seq.singleton sub2) ~exp_conds:[] in
  let env2 = Env.set_freshen env2 true in
  let _, env2 = Pre.init_vars pre_regs env2 in
  let env1 = Pre.mk_env ctx var_gen ~subs:(Seq.singleton sub1)
      ~exp_conds:[Pre.mem_read_offsets env2 offset] in
  let _, env1 = Pre.init_vars pre_regs env1 in
  let post1, hyps1 = Comp.compare_subs_sp in
  let post2, hyps2 = Comp.compare_subs_eq ~pre_regs ~post_regs in
  let compare_prop, env1, env2 = Comp.compare_subs
      ~postconds:[post1; post2] ~hyps:[hyps1; hyps2]
      ~original:(sub1, env1) ~modified:(sub2, env2)
  in
  assert_z3_compare test_ctx ~orig:env1 ~modif:env2
    (Sub.to_string sub1) (Sub.to_string sub2)
    compare_prop Z3.Solver.UNSATISFIABLE


(* RAX := mem[0x600160, el]:u64
   vs
   RAX := mem[0x600161, el]:u64 *)
let test_memory_model_2 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let module Target = (val target_of_arch `x86_64) in
  let mem = Target.CPU.mem in
  let rax = Var.create "RAX" reg64_t in
  let addr1 = 0x600160 in
  let addr2 = 0x600161 in
  let sub1 = Bil.(
      [ rax := load ~mem:(var mem) ~addr:(i64 addr1) LittleEndian `r64; ]
    ) |> bil_to_sub in
  let sub2 = Bil.(
      [ rax := load ~mem:(var mem) ~addr:(i64 addr2) LittleEndian `r64; ]
    ) |> bil_to_sub in
  let offset = fun addr ->
    let width = addr |> Z3.Expr.get_sort |> Z3.BitVector.get_size in
    let offset = Z3.BitVector.mk_numeral ctx "22" width in
    Z3.BitVector.mk_add ctx addr offset
  in
  let pre_regs = Var.Set.of_list [rax; mem] in
  let post_regs = Var.Set.singleton rax in
  let env2 = Pre.mk_env ctx var_gen ~subs:(Seq.singleton sub2) ~exp_conds:[] in
  let env2 = Env.set_freshen env2 true in
  let _, env2 = Pre.init_vars pre_regs env2 in
  let env1 = Pre.mk_env ctx var_gen ~subs:(Seq.singleton sub1)
      ~exp_conds:[Pre.mem_read_offsets env2 offset] in
  let _, env1 = Pre.init_vars pre_regs env1 in
  let post1, hyps1 = Comp.compare_subs_sp in
  let post2, hyps2 = Comp.compare_subs_eq ~pre_regs ~post_regs in
  let compare_prop, env1, env2 = Comp.compare_subs
      ~postconds:[post1; post2] ~hyps:[hyps1; hyps2]
      ~original:(sub1, env1) ~modified:(sub2, env2)
  in
  assert_z3_compare test_ctx ~orig:env1 ~modif:env2
    (Sub.to_string sub1) (Sub.to_string sub2)
    compare_prop Z3.Solver.SATISFIABLE


(* RAX := 0x600160
   RAX := mem[RAX, el]:u64
   vs
   RAX := 0x600161
   RAX := mem[RAX, el]:u64 *)
let test_memory_model_3 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let module Target = (val target_of_arch `x86_64) in
  let mem = Target.CPU.mem in
  let rax = Var.create "RAX" reg64_t in
  let addr1 = 0x600160 in
  let addr2 = 0x600161 in
  let sub1 = Bil.(
      [
        rax := i64 addr1;
        rax := load ~mem:(var mem) ~addr:(var rax) LittleEndian `r64;
      ]
    ) |> bil_to_sub in
  let sub2 = Bil.(
      [
        rax := i64 addr2;
        rax := load ~mem:(var mem) ~addr:(var rax) LittleEndian `r64;
      ]
    ) |> bil_to_sub in
  let offset = fun addr ->
    let width = addr |> Z3.Expr.get_sort |> Z3.BitVector.get_size in
    let offset = Z3.BitVector.mk_numeral ctx "1" width in
    Z3.BitVector.mk_add ctx addr offset
  in
  let pre_regs = Var.Set.of_list [rax; mem] in
  let post_regs = Var.Set.singleton rax in
  let env2 = Pre.mk_env ctx var_gen ~subs:(Seq.singleton sub2) ~exp_conds:[] in
  let env2 = Env.set_freshen env2 true in
  let _, env2 = Pre.init_vars pre_regs env2 in
  let env1 = Pre.mk_env ctx var_gen ~subs:(Seq.singleton sub1)
      ~exp_conds:[Pre.mem_read_offsets env2 offset] in
  let _, env1 = Pre.init_vars pre_regs env1 in
  let post1, hyps1 = Comp.compare_subs_sp in
  let post2, hyps2 = Comp.compare_subs_eq ~pre_regs ~post_regs in
  let compare_prop, env1, env2 = Comp.compare_subs
      ~postconds:[post1; post2] ~hyps:[hyps1; hyps2]
      ~original:(sub1, env1) ~modified:(sub2, env2)
  in
  assert_z3_compare test_ctx ~orig:env1 ~modif:env2
    (Sub.to_string sub1) (Sub.to_string sub2)
    compare_prop Z3.Solver.UNSATISFIABLE


let test_mk_smtlib2_compare_1 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env1 = Pre.mk_env ctx var_gen in
  let env2 = Pre.mk_env ctx var_gen in
  let env2 = Env.set_freshen env2 true in
  let x = Var.create "x" reg32_t in
  let y = Var.create "y" reg32_t in
  let x1, env1 = Env.get_var env1 x in
  let _, env2 = Env.get_var env2 x in
  let _, env1 = Env.get_var env1 y in
  let y2, env2 = Env.get_var env2 y in
  let init_x1, env1 = Env.mk_init_var env1 x in
  let _, env2 = Env.mk_init_var env2 x in
  let _, env1 = Env.mk_init_var env1 y in
  let init_y2, env2 = Env.mk_init_var env2 y in
  let cond = "(assert (and (= x_orig init_x_orig) (= y_mod init_y_mod)))" in
  let expected =
    let constr =
      Bool.mk_and ctx [Bool.mk_eq ctx x1 init_x1; Bool.mk_eq ctx y2 init_y2]
      |> Constr.mk_goal "(and (= x0 init_x0) (= y02 init_y02))"
      |> Constr.mk_constr
    in
    Constr.mk_clause [] [constr]
  in
  let result = Compare.mk_smtlib2_compare env1 env2 cond in
  assert_equal ~ctxt:test_ctx
    ~printer:Constr.to_string
    expected result


let test_mk_smtlib2_compare_2 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env1 = Pre.mk_env ctx var_gen in
  let env2 = Pre.mk_env ctx var_gen in
  let env2 = Env.set_freshen env2 true in
  let x = Var.create "x" reg32_t in
  let x1, env1 = Env.get_var env1 x in
  let x2, env2 = Env.get_var env2 x in
  let _, env1 = Env.mk_init_var env1 x in
  let init_x2, env2 = Env.mk_init_var env2 x in
  let x_orig123 = BV.mk_const_s ctx "x_orig123" 32 in
  let cond =
    "(declare-const x_orig123 (_ BitVec 32)) \n\
     (assert (and (= x_orig x_orig123) (= x_mod init_x_mod)))"
  in
  let expected =
    let constr =
      Bool.mk_and ctx [Bool.mk_eq ctx x1 x_orig123; Bool.mk_eq ctx x2 init_x2]
      |> Constr.mk_goal "(and (= x0 x_orig123) (= x01 init_x01))"
      |> Constr.mk_constr
    in
    Constr.mk_clause [] [constr]
  in
  let result = Compare.mk_smtlib2_compare env1 env2 cond in
  assert_equal ~ctxt:test_ctx
    ~printer:Constr.to_string
    expected result


let suite = [
  "z = x+y; and x = x+1; y = y-1; z = x+y;"  >:: test_block_pair_1;
  "z = x; and y = x; z = y;"                 >:: test_block_pair_2;

  "Remove dead assignments"                  >:: test_sub_pair_1;
  "Remove needed assignments"                >:: test_sub_pair_2;
  "Arithmetic across different blocks"       >:: test_sub_pair_3;
  "Squashing assignments"                    >:: test_sub_pair_4;
  "Jump to opposite block"                   >:: test_sub_pair_5;
  "Assert in original, VC in modified UNSAT" >:: test_sub_pair_6;
  "Assert in original, VC in modified SAT"   >:: test_sub_pair_7;

  "Same subroutines"                         >:: test_sub_pair_fun_1;
  "Fun called in modified sub"               >:: test_sub_pair_fun_2;
  "Branches with fun calls"                  >:: test_sub_pair_fun_3;
  "Fun called in branch"                     >:: test_sub_pair_fun_4;

  "Function output substitution: UNSAT"      >:: test_fun_outputs_1;
  "Function output substitution: SAT"        >:: test_fun_outputs_2;
  "Function output: all input regs SAT"      >:: test_fun_outputs_3;
  "Function output: no input regss UNSAT"    >:: test_fun_outputs_4;

  "Compare memory layout"                    >:: test_sub_pair_mem_1;

  "Diff data location: UNSAT"                >:: test_memory_model_1;
  "Diff data location: SAT"                  >:: test_memory_model_2;
  "Diff data location, substitution: UNSAT"  >:: test_memory_model_3;

  "Parsing smtlib compare expression"        >:: test_mk_smtlib2_compare_1;
  "Should not overwrite x_orig123"           >:: test_mk_smtlib2_compare_2;
]
