open !Core
open Bap.Std
open Graphlib.Std
open OUnit2
open Testing_utilities
open Bap_wp
open Cfg_path

module Pre = Precondition
module Comp = Compare
module Constr = Constraint
module Env = Environment
module Bool = Z3.Boolean
module BV = Z3.BitVector
module Out = Output
module CP = Cfg_path

(* utility functions from test_compare.ml *)

let assert_z3_compare (test_ctx : test_ctxt) (body1 : string) (body2 : string)
    (pre : Constr.t) (expected : Z3.Solver.status) ~orig:(env1 : Env.t)
    ~modif:(env2 : Env.t) : unit =
  let z3_ctx = Env.get_context env1 in
  let solver = Z3.Solver.mk_simple_solver z3_ctx in
  let result = Pre.check solver z3_ctx pre in
  assert_equal ~ctxt:test_ctx
    ~printer:Z3.Solver.string_of_status
    ~pp_diff:(fun ff (exp, real) ->
        Format.fprintf ff "\n\nComparing:\n%s\nand\n\n%s\nCompare_prop:\n%a\n\n%!"
          body1 body2 (Constr.pp ()) pre;
        print_z3_model solver exp real pre ~orig:env1 ~modif:env2)
    expected result

let code_of_sub sub env = Comp.{
    env;
    prog = sub;
    mem = Memmap.empty;
    code_addrs = Utils.Code_addrs.empty; }

let test_sub_pair_1 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env1 = Pre.mk_env ~target:test_tgt ctx var_gen in
  let env2 = Pre.mk_env ~target:test_tgt ctx var_gen in
  let blk1 = Blk.create () in
  let blk2 = Blk.create () in
  let blk3 = Blk.create () in
  let blk4 = Blk.create () in
  let blk1' = Blk.create () in
  let blk2' = Blk.create () in
  let blk3' = Blk.create () in
  let blk4' = Blk.create () in
  let x = Var.create "x" reg32_t in
  let y = Var.create "y" reg32_t in
  let z = Var.create "z" reg32_t in
  let lt = Bil.( (var x) < (i32 1) ) in
  let blk1  = blk1 |> mk_cond lt blk2 blk3 in
  let blk1' = blk1' |> mk_cond lt blk2' blk3' in
  let blk2 = blk2
             |> mk_def y one
             |> mk_jmp blk4
  in
  let blk2' = blk2'
              |> mk_def y one
              |> mk_jmp blk4'
  in
  let blk3 = blk3
             |> mk_def y two
             |> mk_jmp blk4
  in
  let blk3' = blk3'
              |> mk_def y two
              |> mk_jmp blk4'
  in
  let blk4 = blk4
             |> mk_def y (Bil.var x)
             |> mk_def z (Bil.var y)
  in
  (* different from blk4 in that y def is removed *)
  let blk4' = blk4'
              |> mk_def z (Bil.var y)
  in
  let sub1 = mk_sub [blk1; blk2; blk3; blk4] in
  let sub2 = mk_sub [blk1'; blk2'; blk3'; blk4'] in
  let pre_regs = Var.Set.union (Var.Set.singleton x) (Var.Set.singleton y) in
  let post_regs = Var.Set.singleton z in
  let post, hyps = Comp.compare_subs_eq ~pre_regs ~post_regs in
  let compare_prop, env1, env2 = Comp.compare_subs
      ~postconds:[post] ~hyps:[hyps]
      ~original:(code_of_sub sub1 env1) ~modified:(code_of_sub sub2 env2) in
  let z3_ctx = Env.get_context env1 in
  let solver = Z3.Solver.mk_simple_solver z3_ctx in
  let result = Pre.check solver z3_ctx compare_prop in
  match result with
  | Solver.UNSATISFIABLE -> failwith "err"
  | Solver.UNKNOWN -> failwith "unk"
  | Solver.SATISFIABLE ->
     (* taken from output.ml *)
     let mem1, _ = Env.get_var env1 (Env.get_mem env1) in
     let mem2, _ = Env.get_var env2 (Env.get_mem env2) in
     let refuted_goals =
       Constr.get_refuted_goals compare_prop solver z3_ctx ~filter_out:[mem1; mem2] in
     pp_cfg_path_fst_refuted_goal refuted_goals sub1 sub2 "sub_1a.dot" "sub_1b.dot"

let test_sub_pair_2 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env1 = Pre.mk_env ~target:test_tgt ctx var_gen in
  let env2 = Pre.mk_env ~target:test_tgt ctx var_gen in
  let blk1 = Blk.create () in
  let blk1' = Blk.create () in
  let blk2  = Blk.create () in
  let blk2' = Blk.create () in
  let blk3  = Blk.create () in
  let blk3' = Blk.create () in
  let blk4  = Blk.create () in
  let blk4' = Blk.create () in
  let x = Var.create "x" reg32_t in
  let y = Var.create "y" reg32_t in
  let lt = Bil.( (var x) < (i32 1) ) in
  
  let blk1  = blk1  |> mk_def x two |> mk_cond lt blk2 blk3 in
  let blk1' = blk1'                 |> mk_cond lt blk2' blk3' in

  let blk2 = blk2   |> mk_def y one |> mk_jmp blk4 in 
  let blk2' = blk2' |> mk_def y one |> mk_jmp blk4' in

  let blk3 = blk3   |> mk_def y two |> mk_jmp blk4 in
  let blk3' = blk3' |> mk_def y two |> mk_jmp blk4' in

  let sub1 = mk_sub [blk1;  blk2;  blk3;  blk4] in
  let sub2 = mk_sub [blk1'; blk2'; blk3'; blk4'] in
  
  let pre_regs = Var.Set.union (Var.Set.singleton x) (Var.Set.singleton y) in
  let post_regs = Var.Set.singleton y in
  let post, hyps = Comp.compare_subs_eq ~pre_regs ~post_regs in
  let compare_prop, env1, env2 = Comp.compare_subs
      ~postconds:[post] ~hyps:[hyps]
      ~original:(code_of_sub sub1 env1) ~modified:(code_of_sub sub2 env2) in
  let z3_ctx = Env.get_context env1 in
  let solver = Z3.Solver.mk_simple_solver z3_ctx in
  let result = Pre.check solver z3_ctx compare_prop in
  match result with
  | Solver.UNSATISFIABLE -> failwith "err"
  | Solver.UNKNOWN -> failwith "unk"
  | Solver.SATISFIABLE ->
     let mem1, _ = Env.get_var env1 (Env.get_mem env1) in
     let mem2, _ = Env.get_var env2 (Env.get_mem env2) in
     let refuted_goals =
       Constr.get_refuted_goals compare_prop solver z3_ctx ~filter_out:[mem1; mem2] in
     pp_cfg_path_fst_refuted_goal refuted_goals sub1 sub2 "sub_2a.dot" "sub_2b.dot"

(* test with a loop *)
let test_sub_pair_3 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env1 = Pre.mk_env ~target:test_tgt ctx var_gen in
  let env2 = Pre.mk_env ~target:test_tgt ctx var_gen in
  let blk1 = Blk.create () in
  let blk1' = Blk.create () in
  let blk2  = Blk.create () in
  let blk2' = Blk.create () in
  let blk3  = Blk.create () in
  let blk3' = Blk.create () in
  let blk4  = Blk.create () in
  let blk4' = Blk.create () in
  let x = Var.create "x" reg32_t in
  let eq1 = Bil.( (var x) = (i32 3) ) in
  let eq2 = Bil.( (var x) = (i32 8) ) in
  let inc = Bil.( (var x) + (i32 1) ) in
  
  let blk1  = blk1  |> mk_def x one |> mk_jmp blk2  in
  let blk1' = blk1' |> mk_def x one |> mk_jmp blk2' in

  let blk2  = blk2  |> mk_cond eq1 blk4 blk3   in
  let blk2' = blk2' |> mk_cond eq2 blk4' blk3' in
  
  let blk3  = blk3  |> mk_def x inc |> mk_jmp blk2  in
  let blk3' = blk3' |> mk_def x inc |> mk_jmp blk2' in

  let sub1 = mk_sub [blk1;  blk2;  blk3;  blk4] in
  let sub2 = mk_sub [blk1'; blk2'; blk3'; blk4'] in

  let pre_regs = Var.Set.singleton x in
  let post_regs = Var.Set.singleton x in
  let post, hyps = Comp.compare_subs_eq ~pre_regs ~post_regs in
  let compare_prop, env1, env2 = Comp.compare_subs
      ~postconds:[post] ~hyps:[hyps]
      ~original:(code_of_sub sub1 env1) ~modified:(code_of_sub sub2 env2) in
  let z3_ctx = Env.get_context env1 in
  let solver = Z3.Solver.mk_simple_solver z3_ctx in
  let result = Pre.check solver z3_ctx compare_prop in
  match result with
  | Solver.UNSATISFIABLE -> failwith "err"
  | Solver.UNKNOWN -> failwith "unk"
  | Solver.SATISFIABLE ->
     let mem1, _ = Env.get_var env1 (Env.get_mem env1) in
     let mem2, _ = Env.get_var env2 (Env.get_mem env2) in
     let refuted_goals =
       Constr.get_refuted_goals compare_prop solver z3_ctx ~filter_out:[mem1; mem2] in
     pp_cfg_path_fst_refuted_goal refuted_goals sub1 sub2 "sub_3a.dot" "sub_3b.dot"

let suite = [
    "Remove needed assignments" >:: test_sub_pair_1;
    "Remove hard-coded x value" >:: test_sub_pair_2;
    "Different loop bounds"     >:: test_sub_pair_3
]
