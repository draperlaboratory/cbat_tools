open !Core
open Bap.Std
open OUnit2
open Testing_utilities
open Bap_wp

module Pre = Precondition
module Comp = Compare
module Constr = Constraint
module Env = Environment
module Bool = Z3.Boolean
module BV = Z3.BitVector
module Out = Output
module CP = Cfg_path
module Node = Graphs.Ir.Node
module Edge = Graphs.Ir.Edge
module EdgeSet = Edge.Set
module Graph = Graphs.Ir

let code_of_sub sub env = Comp.{
    env;
    prog = sub;
    mem = Memmap.empty;
    code_addrs = Utils.Code_addrs.empty; }

let string_of_edgeset (es : EdgeSet.t) : string =
  EdgeSet.fold es ~init:"\n" ~f:(fun s e -> s ^ Graphs.Ir.Edge.to_string e ^ "\n")

let edge_of_endpoints (src : Blk.t) (dst : Blk.t) : Edge.t =
  let cfg = [src; dst] |> mk_sub |> Sub.to_cfg in
  let es = Graph.edges cfg |> Seq.to_list in
  match es with
  | [e] -> e
  | _   -> failwith "CFG should consist of a single edge"

(* TODO : refactor tests below in terms of this function *)
let validate_taken_edges (sub1 : Sub.t) (sub2 : Sub.t)
      ~(pre_regs : Var.Set.t) ~(post_regs : Var.Set.t)
    ~(expected1 : EdgeSet.t) ~(expected2 : EdgeSet.t) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env1 = Pre.mk_env ~target:test_tgt ctx var_gen in
  let env2 = Pre.mk_env ~target:test_tgt ctx var_gen in
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
     match Seq.hd refuted_goals with
     | None -> assert_failure "expected at least one refuted goal after SAT result"
     | Some rg ->
        let es1, es2 = CP.taken_edges_of_refuted_goal rg sub1 sub2 in
        let assert_equal_sets (exp : EdgeSet.t) (act : EdgeSet.t) =
          assert_equal exp act ~cmp:EdgeSet.equal ~printer:string_of_edgeset in
        begin
          assert_equal_sets expected1 es1;
          assert_equal_sets expected2 es2
        end
       
(** 

sub #1:

1:
x := 0
when x < 1 goto 2
goto 3

2:
y := 1
goto 4

3:
y := 2
goto 4

4:
y := x
z := y

sub #2:

1:
x := 0
when x < 1 goto 2
goto 3

2:
y := 1
goto 4

3:
y := 2
goto 4

4:
z := y

*)
let test_sub_pair_1 (_ : test_ctxt) : unit =
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
  let blk1  = blk1
              |> mk_def x zero
              |> mk_cond lt blk2 blk3 in
  let blk1' = blk1'
              |> mk_def x zero
              |> mk_cond lt blk2' blk3' in
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
  let expected1 =
    EdgeSet.of_list [edge_of_endpoints blk1 blk2; edge_of_endpoints blk2 blk4] in
  let expected2 =
    EdgeSet.of_list [edge_of_endpoints blk1' blk2'; edge_of_endpoints blk2' blk4'] in
  validate_taken_edges sub1 sub2 ~pre_regs ~post_regs ~expected1 ~expected2

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

  let expected1 =
    EdgeSet.of_list [edge_of_endpoints blk1 blk3; edge_of_endpoints blk3 blk4] in
  let expected2 =
    EdgeSet.of_list [edge_of_endpoints blk1' blk2'; edge_of_endpoints blk2' blk4'] in
  
  validate_taken_edges sub1 sub2 ~pre_regs ~post_regs ~expected1 ~expected2

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
  ()
(*
let test_sub_pair_3 (_ : test_ctxt) : unit =
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

  let expected1 =
    EdgeSet.of_list [edge_of_endpoints blk1 blk2; edge_of_endpoints blk2 blk3; edge_of_endpoints blk3 blk2; edge_of_endpoints blk3 blk4] in
  let expected2 = EdgeSet.empty in
  validate_taken_edges sub1 sub2 ~pre_regs ~post_regs ~expected1 ~expected2
  *)
let suite = [
    "Remove needed assignments" >:: test_sub_pair_1;
    "Remove hard-coded x value" >:: test_sub_pair_2;
    "Different loop bounds"     >:: test_sub_pair_3
]
