open !Core
open Bap.Std
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

let code_of_sub sub env = Comp.{
    env;
    prog = sub;
    mem = Memmap.empty;
    code_addrs = Utils.Code_addrs.empty; }

(* 
sub #1:

0000008f:
00000097: when x < 1 goto %00000090
00000098: goto %00000091

00000090:
0000009b: y := 1
0000009c: goto %00000092

00000091:
0000009f: y := 2
000000a0: goto %00000092

00000092:
000000a3: y := x
000000a4: z := y

sub #2:

0000004f:
00000055: when x < 1 goto %00000050
00000056: goto %00000051

00000050:
00000059: y := 1
0000005a: goto %00000052

00000051:
0000005d: y := 2
0000005e: goto %00000052

00000052:
00000061: z := y
*)
let test_sub_pair_1 (_ : test_ctxt) : unit =
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
     let mem1, _ = Env.get_var env1 (Env.get_mem env1) in
     let mem2, _ = Env.get_var env2 (Env.get_mem env2) in
     let refuted_goals =
       Constr.get_refuted_goals compare_prop solver z3_ctx ~filter_out:[mem1; mem2] in
     pp_cfg_path_fst_refuted_goal
       refuted_goals ~f:sub1 ~g:sub2 ~f_out:"sub_1a.dot" ~g_out:"sub_1b.dot"

(* 
sub #1:

0000006c:
00000074: x := 2
00000075: when x < 1 goto %0000006e
00000076: goto %00000070

0000006e:
00000079: y := 1
0000007a: goto %00000072

00000070:
0000007d: y := 2
0000007e: goto %00000072

00000072:

sub #2:

0000007d:
00000087: when x < 1 goto %0000007f
00000088: goto %00000081

0000007f:
0000008b: y := 1
0000008c: goto %00000083

00000081:
0000008f: y := 2
00000090: goto %00000083

00000083:
*)
let test_sub_pair_2 (_ : test_ctxt) : unit =
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
     pp_cfg_path_fst_refuted_goal refuted_goals
       ~f:sub1 ~g:sub2 ~f_out:"sub_2a.dot" ~g_out:"sub_2b.dot"

(* 
sub #1:

00000083:
0000008b: x := 1
0000008c: goto %00000085

00000085:
0000008f: when x = 3 goto %00000089
00000090: goto %00000087

00000087:
00000093: x := x + 1
00000094: goto %00000085

00000089:


sub #2:

00000055:
0000005e: x := 1
0000005f: goto %00000057

00000057:
00000062: when x = 8 goto %0000005b
00000063: goto %00000059

00000059:
00000066: x := x + 1
00000067: goto %00000057

0000005b:
*)
let test_sub_pair_3 (_ : test_ctxt) : unit =
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

  let () = print_endline @@ Sub.to_string sub2 in

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
     pp_cfg_path_fst_refuted_goal refuted_goals
       ~f:sub1 ~g:sub2 ~f_out:"sub_3a.dot" ~g_out:"sub_3b.dot"

let suite = [
    "Remove needed assignments" >:: test_sub_pair_1;
    "Remove hard-coded x value" >:: test_sub_pair_2;
    "Different loop bounds"     >:: test_sub_pair_3
]
