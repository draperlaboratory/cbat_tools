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

module Pre = Precondition
module Comp = Compare
module Constr = Constraint
module Env = Environment
module Bool = Z3.Boolean
module Expr = Z3.Expr
module BV = Z3.BitVector

(* To run these tests: `make test.unit` in bap_wp directory *)

(* Helper functions to assist in building basic blocks and subroutines *)
let zero = Bil.int @@ Word.zero 32
let one = Bil.int @@ Word.one 32
let two = Bil.int @@ Word.of_int 2 ~width:32

let mk_def ?tid:(tid = Tid.create ()) (var : var) (exp : exp) (block : Blk.t) : Blk.t =
  Term.append def_t block (Def.create ~tid:tid var exp)

let mk_phi (phi : Phi.t) (block : Blk.t) : Blk.t =
  Term.append phi_t block phi

let mk_jmp ?tid:(tid = Tid.create ()) (dst : Blk.t) (src : Blk.t) : Blk.t =
  Term.append jmp_t src (Jmp.create_goto ~tid:tid (Label.direct (Term.tid dst)))

let mk_call ?tid:(tid = Tid.create ()) (return : label) (target : label) (block : Blk.t) : Blk.t =
  let call = Call.create ~return:return ~target:target () in
  Term.append jmp_t block (Jmp.create_call ~tid:tid call)

let mk_int ?tid:(tid = Tid.create ()) (i : int) (return : Blk.t) (block : Blk.t) :
  Blk.t =
  Term.append jmp_t block (Jmp.create_int ~tid:tid i (Term.tid return))

let mk_cond ?tid:(tid = Tid.create ()) (cond : exp) (t : 'a Term.t) (f : 'b Term.t) (block : Blk.t) : Blk.t =
  let jmp_true = Jmp.create_goto ~tid:tid ~cond:cond (Label.direct (Term.tid t)) in
  let jmp_false = Jmp.create_goto (Label.direct (Term.tid f)) in
  Term.append jmp_t (Term.append jmp_t block jmp_true) jmp_false

let mk_arg ~intent v = Bap.Std.Arg.create ~intent:intent
    (Var.create ~fresh:true "arg" (Var.typ v)) (Bil.var v)

let mk_sub ?tid:(tid = Tid.create ()) ?args:(args = []) ?name:(name = "")
    (blocks : Blk.t list) : Sub.t =
  let blk_build = Sub.Builder.create ~tid:tid ~name:name () in
  List.iter blocks ~f:(Sub.Builder.add_blk blk_build);
  List.iter args ~f:(Sub.Builder.add_arg blk_build);
  Sub.Builder.result blk_build

let mk_z3_expr e env = let e, _, _ = Pre.exp_to_z3 e env in e

let format_log_error (body : string) (pre : Constr.t) (post : Constr.t) : string =
  Format.asprintf "Post:\n%a\n\nAnalyzing:\n%sPre:\n%a\n"
    Constr.pp_constr post body Constr.pp_constr pre

let format_cmp_error (body1 : string) (body2 : string) (pre : Constr.t) : string =
  Format.asprintf "Comparing:\n%s\nand\n\n%s\nCompare_prop:\n%a\n"
    body1 body2 Constr.pp_constr pre

let print_z3_model (ff : Format.formatter) (solver : Z3.Solver.solver)
    (exp : 'a) (real : 'a) : unit =
  if real = exp || real = Z3.Solver.UNSATISFIABLE then () else
    match Z3.Solver.get_model solver with
    | None -> ()
    | Some model -> Format.fprintf ff "\n\nCountermodel:\n%s\n%!" (Z3.Model.to_string model)

let assert_z3_result (test_ctx : test_ctxt) (z3_ctx : Z3.context) (formatter : string)
    (pre : Constr.t) (expected : Z3.Solver.status) : unit =
  let solver = Z3.Solver.mk_simple_solver z3_ctx in
  let pre = Constr.eval pre z3_ctx in
  let is_correct = Bool.mk_implies z3_ctx pre (Bool.mk_false z3_ctx) in
  let result = Z3.Solver.check solver [is_correct] in
  assert_equal ~ctxt:test_ctx
    ~printer:Z3.Solver.string_of_status
    ~pp_diff:(fun ff (exp, real) ->
        Format.fprintf ff "\n\n%s\n%!" formatter;
        print_z3_model ff solver exp real)
    expected result

let i32 n = Bil.int (Word.of_int ~width:32 n)

let test_empty_block (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env = Pre.mk_default_env ctx var_gen in
  let block = Blk.create () in
  let post = Bool.mk_true ctx |> Constr.mk_goal "true" |> Constr.mk_constr in
  let pre, _ = Pre.visit_block env post block in
  let fmtr = format_log_error (Blk.to_string block) pre post in
  assert_z3_result test_ctx ctx fmtr pre Z3.Solver.UNSATISFIABLE


let test_assign_1 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen ()in
  let env = Pre.mk_default_env ctx var_gen in
  let y = Var.create "y" reg32_t in
  let x = Var.create "x" reg32_t in
  let e = Bil.binop Bil.plus (Bil.var x) one in
  let block = Blk.create () |> mk_def y e in
  let post = Bool.mk_eq ctx (Pre.var_to_z3 ctx y) (mk_z3_expr e env)
             |> Constr.mk_goal "y = x + 1"
             |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_block env post block in
  let fmtr = format_log_error (Blk.to_string block) pre post in
  assert_z3_result test_ctx ctx fmtr pre Z3.Solver.UNSATISFIABLE


let test_assign_2 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env = Pre.mk_default_env ctx var_gen in
  let y = Var.create "y" reg32_t in
  let x = Var.create "x" reg32_t in
  let e = Bil.binop Bil.plus (Bil.var x) one in
  let block = Blk.create () |> mk_def y e in
  let post = Bool.mk_eq ctx (Pre.var_to_z3 ctx y) (Pre.var_to_z3 ctx x)
             |> Constr.mk_goal "y = x"
             |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_block env post block in
  let fmtr = format_log_error (Blk.to_string block) pre post in
  assert_z3_result test_ctx ctx fmtr pre Z3.Solver.SATISFIABLE


let test_assign_3 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env = Pre.mk_default_env ctx var_gen in
  let y = Var.create "y" reg32_t in
  let x = Var.create "x" reg32_t in
  let e = Bil.binop Bil.plus (Bil.var x) one in
  let e' = Bil.binop Bil.minus (Bil.var x) one in
  let block = Blk.create ()
              |> mk_def y (Bil.var x)
              |> mk_def x e
  in
  let post = Bool.mk_eq ctx (Pre.var_to_z3 ctx y) (mk_z3_expr e' env)
             |> Constr.mk_goal "y = x - 1"
             |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_block env post block in
  let fmtr = format_log_error (Blk.to_string block) pre post in
  assert_z3_result test_ctx ctx fmtr pre Z3.Solver.UNSATISFIABLE


let test_phi_1 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env = Pre.mk_default_env ctx var_gen in
  let l1_tid = Tid.create () in
  Tid.set_name l1_tid "test_l1";
  let l2_tid = Tid.create () in
  Tid.set_name l2_tid "test_l2";
  let x = Var.create "x" reg32_t in
  let x1 = Var.create "x1" reg32_t in
  let x2 = Var.create "x2" reg32_t in
  let phi_x = Phi.of_list x [(l1_tid, Bil.var x1); (l2_tid, Bil.var x2)] in
  let block = Blk.create () |> mk_phi phi_x in
  let x1_exp = Bool.mk_eq ctx (Pre.var_to_z3 ctx x) (Pre.var_to_z3 ctx x1) in
  let x2_exp = Bool.mk_eq ctx (Pre.var_to_z3 ctx x) (Pre.var_to_z3 ctx x2) in
  let post = Bool.mk_or ctx [x1_exp; x2_exp]
             |> Constr.mk_goal "x = x1 || x = x2"
             |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_block env post block in
  let fmtr = format_log_error (Blk.to_string block) pre post in
  assert_z3_result test_ctx ctx fmtr pre Z3.Solver.UNSATISFIABLE


let test_read_write_1 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env = Pre.mk_default_env ctx var_gen in
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
  let post = Bool.mk_eq ctx (Pre.var_to_z3 ctx y) (Pre.var_to_z3 ctx x)
             |> Constr.mk_goal "y = x"
             |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_block env post block in
  let fmtr = format_log_error (Blk.to_string block) pre post in
  assert_z3_result test_ctx ctx fmtr pre Z3.Solver.UNSATISFIABLE


let test_read_write_2 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env = Pre.mk_default_env ctx var_gen in
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
  let post = Bool.mk_eq ctx (Pre.var_to_z3 ctx y) (Pre.var_to_z3 ctx x)
             |> Constr.mk_goal "y = x"
             |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_block env post block in
  let fmtr = format_log_error (Blk.to_string block) pre post in
  assert_z3_result test_ctx ctx fmtr pre Z3.Solver.UNSATISFIABLE


let test_read_write_3 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env = Pre.mk_default_env ctx var_gen in
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
  let post = Bool.mk_eq ctx (Pre.var_to_z3 ctx y) (Pre.var_to_z3 ctx x)
             |> Constr.mk_goal "y = x"
             |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_block env post block in
  let fmtr = format_log_error (Blk.to_string block) pre post in
  assert_z3_result test_ctx ctx fmtr pre Z3.Solver.SATISFIABLE


let test_read_write_4 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env = Pre.mk_default_env ctx var_gen in
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
  let post = Bool.mk_eq ctx (Pre.var_to_z3 ctx y) (Pre.var_to_z3 ctx x)
             |> Constr.mk_goal "y = x"
             |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_block env post block in
  let fmtr = format_log_error (Blk.to_string block) pre post in
  assert_z3_result test_ctx ctx fmtr pre Z3.Solver.SATISFIABLE


let test_bit_shift_1 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env = Pre.mk_default_env ctx var_gen in
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
  let post = Bool.mk_eq ctx (Pre.var_to_z3 ctx y) (Pre.var_to_z3 ctx x)
             |> Constr.mk_goal "y = x"
             |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_block env post block in
  let fmtr = format_log_error (Blk.to_string block) pre post in
  assert_z3_result test_ctx ctx fmtr pre Z3.Solver.UNSATISFIABLE


let test_bit_shift_2 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env = Pre.mk_default_env ctx var_gen in
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
  let post = Bool.mk_eq ctx (Pre.var_to_z3 ctx y) (Pre.var_to_z3 ctx x)
             |> Constr.mk_goal "y = x"
             |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_block env post block in
  let fmtr = format_log_error (Blk.to_string block) pre post in
  assert_z3_result test_ctx ctx fmtr pre Z3.Solver.SATISFIABLE


let test_bit_ashift_1 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env = Pre.mk_default_env ctx var_gen in
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
  let post = Bool.mk_eq ctx (Pre.var_to_z3 ctx y) (Pre.var_to_z3 ctx x)
             |> Constr.mk_goal "y = x"
             |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_block env post block in
  let fmtr = format_log_error (Blk.to_string block) pre post in
  assert_z3_result test_ctx ctx fmtr pre Z3.Solver.UNSATISFIABLE


let test_bit_ashift_2 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env = Pre.mk_default_env ctx var_gen in
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
  let post = Bool.mk_eq ctx (Pre.var_to_z3 ctx y) (Pre.var_to_z3 ctx x)
             |> Constr.mk_goal "y = x"
             |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_block env post block in
  let fmtr = format_log_error (Blk.to_string block) pre post in
  assert_z3_result test_ctx ctx fmtr pre Z3.Solver.SATISFIABLE


let test_ite_assign_1 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env = Pre.mk_default_env ctx var_gen in
  let x = Var.create "x" reg8_t in
  let y = Var.create "y" reg8_t in
  let lshift = Bil.binop Bil.lshift (Bil.var x) (Bil.int @@ Word.one 8) in
  let rshift = Bil.binop Bil.arshift lshift (Bil.int @@ Word.one 8) in
  let lt = Bil.binop Bil.lt (Bil.var x) (Bil.int @@ Word.of_int 0x40 ~width:8) in
  let ite = Bil.ite ~if_:lt ~then_:rshift ~else_:(Bil.var x) in
  let block = Blk.create ()
              |> mk_def y ite
  in
  let post = Bool.mk_eq ctx (Pre.var_to_z3 ctx y) (Pre.var_to_z3 ctx x)
             |> Constr.mk_goal "y = x"
             |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_block env post block in
  let fmtr = format_log_error (Blk.to_string block) pre post in
  assert_z3_result test_ctx ctx fmtr pre Z3.Solver.UNSATISFIABLE


let test_block_pair_1 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env1 = Pre.mk_default_env ctx var_gen in
  let env2 = Pre.mk_default_env ctx var_gen in
  let x = Var.create "x" reg32_t in
  let y = Var.create "y" reg32_t in
  let z = Var.create "z" reg32_t in
  let blk1 = Blk.create () |> mk_def z (Bil.binop Bil.plus (Bil.var x) (Bil.var y)) in
  let blk2 = Blk.create ()
             |> mk_def x (Bil.binop Bil.plus (Bil.var x) one)
             |> mk_def y (Bil.binop Bil.minus (Bil.var y) one)
             |> mk_def z (Bil.binop Bil.plus (Bil.var x) (Bil.var y))
  in
  let input_vars = Var.Set.union (Var.Set.singleton x) (Var.Set.singleton y) in
  let output_vars = Var.Set.singleton z in
  let compare_prop, _ = Comp.compare_blocks
      ~input:input_vars ~output:output_vars
      ~original:(blk1,env1) ~modified:(blk2,env2) in
  let fmtr = format_cmp_error (Blk.to_string blk1) (Blk.to_string blk2) compare_prop in
  assert_z3_result test_ctx ctx fmtr compare_prop Z3.Solver.UNSATISFIABLE


let test_block_pair_2 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env1 = Pre.mk_default_env ctx var_gen in
  let env2 = Pre.mk_default_env ctx var_gen in
  let x = Var.create "x" reg32_t in
  let y = Var.create "y" reg32_t in
  let z = Var.create "z" reg32_t in
  let blk1 = Blk.create () |> mk_def z (Bil.var x) in
  let blk2 = Blk.create ()
             |> mk_def y (Bil.var x)
             |> mk_def z (Bil.var y)
  in
  let input_vars = Var.Set.singleton x in
  let output_vars = Var.Set.singleton z in
  let compare_prop, _ = Comp.compare_blocks
      ~input:input_vars ~output:output_vars
      ~original:(blk1,env1) ~modified:(blk2,env2) in
  let fmtr = format_cmp_error (Blk.to_string blk1) (Blk.to_string blk2) compare_prop in
  assert_z3_result test_ctx ctx fmtr compare_prop Z3.Solver.UNSATISFIABLE


let test_subroutine_1 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env = Pre.mk_default_env ctx var_gen in
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

  let diff = mk_z3_expr Bil.((var z) - (var x)) env in
  let high  = BV.mk_sle ctx diff (BV.mk_numeral ctx "1" 32) in
  let low = BV.mk_sle ctx (BV.mk_numeral ctx "-1" 32) diff in
  let post = Bool.mk_and ctx [low; high]
             |> Constr.mk_goal "-1 <= z - x && z - x <= 1"
             |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_sub env post sub in
  let fmtr = format_log_error (Sub.to_string sub) pre post in
  assert_z3_result test_ctx ctx fmtr pre Z3.Solver.UNSATISFIABLE


let test_subroutine_1_2 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env = Pre.mk_default_env ctx var_gen in
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
  let env = Env.add_var env x (Pre.var_to_z3 ctx x) in
  let env = Env.add_var env y (Pre.var_to_z3 ctx y) in
  let env = Env.add_var env z (Pre.var_to_z3 ctx z) in
  (* The names x0, y0 and z0 are magical, as they are generated by BAP
     (with the "base names" x, y, z)*)
  let post = Pre.mk_smtlib2_post env
      "(assert (and (bvsle (bvsub z0 x0) #x00000001) (bvsle #xffffffff (bvsub z0 x0))))"
  in
  let pre, _ = Pre.visit_sub env post sub in
  let fmtr = format_log_error (Sub.to_string sub) pre post in
  assert_z3_result test_ctx ctx fmtr pre Z3.Solver.UNSATISFIABLE


let test_subroutine_2 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env = Pre.mk_default_env ctx var_gen in
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
  let diff = mk_z3_expr (Bil.binop Bil.minus (Bil.var x4) (Bil.var x1)) env in
  let high  = BV.mk_sle ctx diff (BV.mk_numeral ctx "1" 32) in
  let low = BV.mk_sle ctx (BV.mk_numeral ctx "-1" 32) diff in
  let post = Bool.mk_and ctx [low; high]
             |> Constr.mk_goal "x4 - x1 <= 1 && -1 <= x4 - x1"
             |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_sub env post sub in
  let fmtr = format_log_error (Sub.to_string sub) pre post in
  assert_z3_result test_ctx ctx fmtr pre Z3.Solver.UNSATISFIABLE


let test_subroutine_3 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env = Pre.mk_default_env ctx var_gen in
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
  let y_exp = Bool.mk_eq ctx (Pre.var_to_z3 ctx x) (Pre.var_to_z3 ctx y) in
  let z_exp = Bool.mk_eq ctx (Pre.var_to_z3 ctx x) (Pre.var_to_z3 ctx z) in
  let post = Bool.mk_or ctx [y_exp; z_exp]
             |> Constr.mk_goal "x = y || x = z"
             |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_sub env post sub in
  let fmtr = format_log_error (Sub.to_string sub) pre post in
  assert_z3_result test_ctx ctx fmtr pre Z3.Solver.UNSATISFIABLE


let test_subroutine_4 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env = Pre.mk_default_env ctx var_gen in
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
  let y_exp = Bool.mk_eq ctx (Pre.var_to_z3 ctx w) (Pre.var_to_z3 ctx y) in
  let z_exp = Bool.mk_eq ctx (Pre.var_to_z3 ctx w) (Pre.var_to_z3 ctx z) in
  let post = Bool.mk_or ctx [y_exp; z_exp]
             |> Constr.mk_goal "x = y || w = z"
             |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_sub env post sub in
  let fmtr = format_log_error (Sub.to_string sub) pre post in
  assert_z3_result test_ctx ctx fmtr pre Z3.Solver.UNSATISFIABLE


let test_subroutine_5 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env = Pre.mk_default_env ctx var_gen in
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
  let post = Bool.mk_eq ctx (Pre.var_to_z3 ctx z) (mk_z3_expr e' env)
             |> Constr.mk_goal "z = y + 1"
             |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_sub env post sub in
  let fmtr = format_log_error (Sub.to_string sub) pre post in
  assert_z3_result test_ctx ctx fmtr pre Z3.Solver.UNSATISFIABLE


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
  let env = Pre.mk_default_env ~subs ctx var_gen in
  let post = Bool.mk_true ctx
             |> Constr.mk_goal "true"
             |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_sub env post sub in
  let fmtr = format_log_error (Sub.to_string sub) pre post in
  assert_z3_result test_ctx ctx fmtr pre Z3.Solver.SATISFIABLE


let test_subroutine_7 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let assert_sub, assert_expr = Bil_to_bir.mk_assert_fail () in
  let sub = Bil_to_bir.bil_to_sub Bil.([jmp assert_expr])  in
  let subs = Seq.singleton assert_sub in
  let env = Pre.mk_default_env ~subs ctx var_gen in
  let post = Bool.mk_true ctx
             |> Constr.mk_goal "true"
             |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_sub env post sub in
  let fmtr = format_log_error (Sub.to_string sub) pre post in
  assert_z3_result test_ctx ctx fmtr pre Z3.Solver.SATISFIABLE


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
  let env = Pre.mk_default_env ctx var_gen
      ~subs:(Seq.of_list [call_body; main_sub]) in
  let post = Bool.mk_eq ctx (mk_z3_expr (Bil.var ret_var) env) (mk_z3_expr zero env)
             |> Constr.mk_goal "ret = 0"
             |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_sub env post main_sub in
  let fmtr = format_log_error (Sub.to_string main_sub) pre post in
  assert_z3_result test_ctx ctx fmtr pre Z3.Solver.SATISFIABLE


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
  let env = Pre.mk_default_env ctx var_gen ~subs:(Seq.of_list [call_body; main_sub]) in
  let post = Bool.mk_const_s ctx "called_test_sub1"
             |> Constr.mk_goal "called_test_sub1"
             |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_sub env post main_sub in
  let fmtr = format_log_error (Sub.to_string main_sub) pre post in
  assert_z3_result test_ctx ctx fmtr pre Z3.Solver.UNSATISFIABLE


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
  let env = Pre.mk_default_env ctx var_gen ~subs:(Seq.of_list [call_body; main_sub]) in
  let post = Bool.mk_const_s ctx "called_test_sub1"
             |> Constr.mk_goal "called_test_sub1"
             |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_sub env post main_sub in
  let fmtr = format_log_error (Sub.to_string main_sub) pre post in
  assert_z3_result test_ctx ctx fmtr pre Z3.Solver.UNSATISFIABLE


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
  let env = Pre.mk_default_env ctx var_gen ~subs:(Seq.of_list [call_body; main_sub]) in
  let post = Bool.mk_const_s ctx "called_test_sub1"
             |> Constr.mk_goal "called_test_sub1"
             |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_sub env post main_sub in
  let fmtr = format_log_error (Sub.to_string main_sub) pre post in
  assert_z3_result test_ctx ctx fmtr pre Z3.Solver.UNSATISFIABLE


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
  let env = Pre.mk_default_env ctx var_gen ~subs:(Seq.of_list [call_body; main_sub]) in
  let post = Bool.mk_eq ctx (Bool.mk_true ctx) (Bool.mk_const_s ctx "called_test_sub1")
             |> Constr.mk_goal "called_test_sub1"
             |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_sub env post main_sub in
  let fmtr = format_log_error (Sub.to_string main_sub) pre post in
  assert_z3_result test_ctx ctx fmtr pre Z3.Solver.SATISFIABLE


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
  let env = Pre.mk_default_env ctx var_gen
      ~subs:(Seq.of_list [call1_body; call2_body; main_sub]) in
  let sub1_called = Option.value_exn (sub1_tid |> Env.get_called env) in
  let sub2_called = Option.value_exn (sub2_tid |> Env.get_called env) in
  let post =
    Bool.mk_or ctx [Bool.mk_const_s ctx sub1_called; Bool.mk_const_s ctx sub2_called]
    |> Constr.mk_goal "sub1_called || sub2_called"
    |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_sub env post main_sub in
  let fmtr = format_log_error (Sub.to_string main_sub) pre post in
  assert_z3_result test_ctx ctx fmtr pre Z3.Solver.UNSATISFIABLE


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
  let env = Pre.mk_inline_env ctx var_gen ~subs:(Seq.of_list [main_sub; call_sub]) in
  let sub_called = Option.value_exn (call_tid |> Env.get_called env) in
  let post = Bool.mk_and ctx [
      Bool.mk_eq ctx (mk_z3_expr Bil.(var x + one) env) (mk_z3_expr (Bil.var z) env);
      Bool.mk_const_s ctx sub_called]
             |> Constr.mk_goal "x + 1 = z && sub_called"
             |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_sub env post main_sub in
  let fmtr = format_log_error ((Sub.to_string main_sub) ^ (Sub.to_string call_sub))
      pre post in
  assert_z3_result test_ctx ctx fmtr pre Z3.Solver.UNSATISFIABLE


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
  let env = Pre.mk_default_env ctx var_gen ~subs:(Seq.of_list [main_sub; call_sub]) in
  let sub_called = Option.value_exn (call_tid |> Env.get_called env) in
  let post = Bool.mk_and ctx [
      Bool.mk_eq ctx (mk_z3_expr Bil.(var x + one) env) (mk_z3_expr (Bil.var z) env);
      Bool.mk_const_s ctx sub_called]
             |> Constr.mk_goal "x + 1 = z && sub_called"
             |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_sub env post main_sub in
  let fmtr = format_log_error ((Sub.to_string main_sub) ^ (Sub.to_string call_sub))
      pre post in
  assert_z3_result test_ctx ctx fmtr pre Z3.Solver.SATISFIABLE


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
  let env = Pre.mk_inline_env ctx var_gen
      ~subs:(Seq.of_list [main_sub; call1_sub; call2_sub]) in
  let sub1_called = Option.value_exn (call1_tid |> Env.get_called env) in
  let sub2_called = Option.value_exn (call2_tid |> Env.get_called env) in
  let post = Bool.mk_and ctx [
      Bool.mk_eq ctx (mk_z3_expr Bil.(var x + two) env) (mk_z3_expr (Bil.var z) env);
      Bool.mk_const_s ctx sub1_called;
      Bool.mk_const_s ctx sub2_called]
             |> Constr.mk_goal "x + 2 = z && sub1_called && sub2_called"
             |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_sub env post main_sub in
  let fmtr = format_log_error
      ((Sub.to_string main_sub) ^ (Sub.to_string call1_sub) ^ (Sub.to_string call2_sub))
      pre post in
  assert_z3_result test_ctx ctx fmtr pre Z3.Solver.UNSATISFIABLE


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
  let env = Pre.mk_default_env ctx var_gen ~subs:(Seq.of_list [main_sub]) in
  let post = Bool.mk_eq ctx (mk_z3_expr (Bil.var ret_var) env) (mk_z3_expr zero env)
             |> Constr.mk_goal "ret = 0"
             |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_sub env post main_sub in
  let fmtr = format_log_error (Sub.to_string main_sub) pre post in
  assert_z3_result test_ctx ctx fmtr pre Z3.Solver.UNSATISFIABLE


let test_sub_pair_1 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env1 = Pre.mk_default_env ctx var_gen in
  let env2 = Pre.mk_default_env ctx var_gen in
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
  let input_vars = Var.Set.union (Var.Set.singleton x) (Var.Set.singleton y) in
  let output_vars = Var.Set.singleton z in
  let compare_prop, _ = Comp.compare_subs_eq
      ~input:input_vars ~output:output_vars
      ~original:(sub1,env1) ~modified:(sub2,env2) in
  let fmtr = format_cmp_error (Sub.to_string sub1) (Sub.to_string sub2) compare_prop in
  assert_z3_result test_ctx ctx fmtr compare_prop Z3.Solver.UNSATISFIABLE


let test_sub_pair_2 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env1 = Pre.mk_default_env ctx var_gen in
  let env2 = Pre.mk_default_env ctx var_gen in
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
  let input_vars = Var.Set.union (Var.Set.singleton x) (Var.Set.singleton y) in
  let output_vars = Var.Set.singleton z in
  let compare_prop, _ = Comp.compare_subs_eq
      ~input:input_vars ~output:output_vars
      ~original:(sub1,env1) ~modified:(sub2,env2) in
  let fmtr = format_cmp_error (Sub.to_string sub1) (Sub.to_string sub2) compare_prop in
  assert_z3_result test_ctx ctx fmtr compare_prop Z3.Solver.SATISFIABLE


let test_sub_pair_3 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env1 = Pre.mk_default_env ctx var_gen in
  let env2 = Pre.mk_default_env ctx var_gen in
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
  let input_vars = Var.Set.union (Var.Set.singleton x) (Var.Set.singleton y) in
  let output_vars = Var.Set.singleton z in
  let compare_prop, _ = Comp.compare_subs_eq
      ~input:input_vars ~output:output_vars
      ~original:(sub1,env1) ~modified:(sub2,env2) in
  let fmtr = format_cmp_error (Sub.to_string sub1) (Sub.to_string sub2) compare_prop in
  assert_z3_result test_ctx ctx fmtr compare_prop Z3.Solver.UNSATISFIABLE


let test_sub_pair_4 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env1 = Pre.mk_default_env ctx var_gen in
  let env2 = Pre.mk_default_env ctx var_gen in
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
  let input_vars = Var.Set.singleton x in
  let output_vars = Var.Set.singleton y in
  let compare_prop, _ = Comp.compare_subs_eq
      ~input:input_vars ~output:output_vars
      ~original:(sub1,env1) ~modified:(sub2,env2) in
  let fmtr = format_cmp_error (Sub.to_string sub1) (Sub.to_string sub2) compare_prop in
  assert_z3_result test_ctx ctx fmtr compare_prop Z3.Solver.UNSATISFIABLE


let test_sub_pair_5 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env1 = Pre.mk_default_env ctx var_gen in
  let env2 = Pre.mk_default_env ctx var_gen in
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
  let input_vars = Var.Set.singleton x in
  let output_vars = Var.Set.singleton y in
  let compare_prop, _ = Comp.compare_subs_eq
      ~input:input_vars ~output:output_vars
      ~original:(sub1,env1) ~modified:(sub2,env2) in
  let fmtr = format_cmp_error (Sub.to_string sub1) (Sub.to_string sub2) compare_prop in
  assert_z3_result test_ctx ctx fmtr compare_prop Z3.Solver.SATISFIABLE


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
  let env1 = Pre.mk_default_env ctx var_gen ~subs:(Seq.of_list [main_sub1; call_sub]) in
  let env2 = Pre.mk_default_env ctx var_gen ~subs:(Seq.of_list [main_sub2; call_sub]) in
  let compare_prop, _ = Comp.compare_subs_fun
      ~original:(main_sub1, env1) ~modified:(main_sub2, env2) in
  let fmtr = format_cmp_error
      (Sub.to_string main_sub1) (Sub.to_string main_sub2) compare_prop in
  assert_z3_result test_ctx ctx fmtr compare_prop Z3.Solver.UNSATISFIABLE


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
  let env1 = Pre.mk_default_env ctx var_gen ~subs:(Seq.of_list [main_sub1; call_sub]) in
  let env2 = Pre.mk_default_env ctx var_gen ~subs:(Seq.of_list [main_sub2; call_sub]) in
  let compare_prop, _ = Comp.compare_subs_fun
      ~original:(main_sub1, env1) ~modified:(main_sub2, env2) in
  let fmtr = format_cmp_error
      (Sub.to_string main_sub1) (Sub.to_string main_sub2) compare_prop in
  assert_z3_result test_ctx ctx fmtr compare_prop Z3.Solver.SATISFIABLE


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
  let env1 = Pre.mk_default_env ctx var_gen
      ~subs:(Seq.of_list [main_sub1; call1_sub; call2_sub]) in
  let env2 = Pre.mk_default_env ctx var_gen
      ~subs:(Seq.of_list [main_sub2; call1_sub; call2_sub]) in
  let compare_prop, _ = Comp.compare_subs_fun
      ~original:(main_sub1, env1) ~modified:(main_sub2, env2) in
  let fmtr = format_cmp_error
      (Sub.to_string main_sub1) (Sub.to_string main_sub2) compare_prop in
  assert_z3_result test_ctx ctx fmtr compare_prop Z3.Solver.SATISFIABLE


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
  let env1 = Pre.mk_default_env ctx var_gen
      ~subs:(Seq.of_list [main_sub1; call1_sub; call2_sub]) in
  let env2 = Pre.mk_default_env ctx var_gen
      ~subs:(Seq.of_list [main_sub2; call1_sub; call2_sub]) in
  let compare_prop, _ = Comp.compare_subs_fun
      ~original:(main_sub1, env1) ~modified:(main_sub2, env2) in
  let fmtr = format_cmp_error
      (Sub.to_string main_sub1) (Sub.to_string main_sub2) compare_prop in
  assert_z3_result test_ctx ctx fmtr compare_prop Z3.Solver.SATISFIABLE


let test_loop_1 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env = Pre.mk_default_env ctx var_gen in
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

  let post = Bool.mk_eq ctx (mk_z3_expr x_y env) (mk_z3_expr a_b env)
             |> Constr.mk_goal "x + y = a + b"
             |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_sub env post sub in
  let fmtr = format_log_error (Sub.to_string sub) pre post in
  assert_z3_result test_ctx ctx fmtr pre Z3.Solver.UNSATISFIABLE


let test_loop_2 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env = Pre.mk_default_env ctx var_gen in
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
  let post = Bool.mk_eq ctx (Pre.var_to_z3 ctx x) (BV.mk_numeral ctx "5" 32)
             |> Constr.mk_goal "x = 5"
             |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_sub env post sub in
  let fmtr = format_log_error (Sub.to_string sub) pre post in
  assert_z3_result test_ctx ctx fmtr pre Z3.Solver.UNSATISFIABLE


let test_loop_3 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env = Pre.mk_default_env ctx var_gen in
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
  let post = Bool.mk_eq ctx (Pre.var_to_z3 ctx x) (BV.mk_numeral ctx "7" 32)
             |> Constr.mk_goal "x = 7"
             |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_sub env post sub in
  let fmtr = format_log_error (Sub.to_string sub) pre post in
  assert_z3_result test_ctx ctx fmtr pre Z3.Solver.SATISFIABLE


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
  let env = Pre.mk_default_env ctx var_gen in
  let bil_var = Bil.int @@ Word.of_int value ~width:width_orig in
  let bil_cast = Bil.cast cast width_cast bil_var in
  let z3_var = Expr.simplify (mk_z3_expr bil_var env) None in
  let z3_cast = Expr.simplify (mk_z3_expr bil_cast env) None in
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


let test_exp_cond_1 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env = Pre.mk_default_env ctx var_gen ~exp_conds:[Pre.non_null_vc] in
  let blk = Blk.create () in
  let addr = Var.create "addr" reg32_t in
  let mem = Var.create "mem" (mem32_t `r8) in
  let x = Var.create "x" reg8_t in
  let load = Bil.load ~mem:(Bil.var mem) ~addr:(Bil.var addr) BigEndian `r8 in
  let blk = blk |> mk_def x load in
  let post = Bool.mk_true ctx
             |> Constr.mk_goal "true"
             |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_block env post blk in
  let fmtr = format_log_error (Blk.to_string blk) pre post in
  assert_z3_result test_ctx ctx fmtr pre Z3.Solver.SATISFIABLE


let test_exp_cond_2 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env = Pre.mk_default_env ctx var_gen ~exp_conds:[Pre.non_null_vc] in
  let blk = Blk.create () in
  let addr = Var.create "addr" reg32_t in
  let mem = Var.create "mem" (mem32_t `r8) in
  let x = Var.create "x" reg8_t in
  let load = Bil.load ~mem:(Bil.var mem) ~addr:(Bil.var addr) BigEndian `r8 in
  let blk = blk
            |> mk_def addr (Bil.int @@ Word.of_int 0x40000000 ~width:32)
            |> mk_def x load in
  let post = Bool.mk_true ctx
             |> Constr.mk_goal "true"
             |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_block env post blk in
  let fmtr = format_log_error (Blk.to_string blk) pre post in
  assert_z3_result test_ctx ctx fmtr pre Z3.Solver.UNSATISFIABLE

let test_subroutine_8 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env = Pre.mk_default_env ctx var_gen ~exp_conds:[Pre.non_null_assert] in
  let mem = Var.create "mem" (mem32_t `r32) in
  let loc = Var.create "loc" reg32_t in
  let read = Bil.(load ~mem:(var mem) ~addr:(var loc) LittleEndian `r32) in
  let sub = Bil.([if_ (read = i32 12)[][]]) |> bil_to_sub in
  let post = Bool.mk_distinct ctx [(Pre.var_to_z3 ctx loc); (BV.mk_numeral ctx "0" 32)]
             |> Constr.mk_goal "loc <> 0"
             |> Constr.mk_constr
  in
  let pre, _ = Pre. visit_sub env post sub in
  let fmtr = format_log_error (Sub.to_string sub) pre post in
  assert_z3_result test_ctx ctx fmtr pre Z3.Solver.UNSATISFIABLE


let test_sub_pair_6 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env1 = Pre.mk_default_env ctx var_gen ~exp_conds:[Pre.non_null_assert] in
  let env2 = Pre.mk_default_env ctx var_gen ~exp_conds:[Pre.non_null_vc] in
  let mem = Var.create "mem" (mem32_t `r32) in
  let loc = Var.create "loc" reg32_t in
  let read = Bil.(load ~mem:(var mem) ~addr:(var loc) LittleEndian `r32) in
  let sub1 = Bil.([if_ (read = i32 12)[][]]) |> bil_to_sub in
  let sub2 = Bil.([if_ (read = i32 3) [if_ (read = i32 4) [][]] []]) |> bil_to_sub in
  let vars = Var.Set.of_list [mem; loc] in
  let compare_prop, _ = Comp.compare_subs_empty_post ~input:vars
      ~original:(sub1, env1) ~modified:(sub2, env2) in
  let fmtr = format_cmp_error
      (Sub.to_string sub1) (Sub.to_string sub2) compare_prop in
  assert_z3_result test_ctx ctx fmtr compare_prop Z3.Solver.UNSATISFIABLE


let test_sub_pair_7 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let env1 = Pre.mk_default_env ctx var_gen ~exp_conds:[Pre.non_null_assert] in
  let env2 = Pre.mk_default_env ctx var_gen ~exp_conds:[Pre.non_null_vc] in
  let mem = Var.create "mem" (mem32_t `r32) in
  let loc = Var.create "loc" reg32_t in
  let read = Bil.(load ~mem:(var mem) ~addr:(var loc) LittleEndian `r32) in
  let read' = Bil.(load ~mem:(var mem) ~addr:(var loc + one) LittleEndian `r32) in
  let sub1 = Bil.([if_ (read = i32 3)[][]]) |> bil_to_sub in
  let sub2 = Bil.([if_ (read = i32 3) [if_ (read' = i32 4) [][]] []]) |> bil_to_sub in
  let vars = Var.Set.of_list [mem; loc] in
  let compare_prop, _ = Comp.compare_subs_empty_post ~input:vars
      ~original:(sub1, env1) ~modified:(sub2, env2) in
  let fmtr = format_cmp_error
      (Sub.to_string sub1) (Sub.to_string sub2) compare_prop in
  assert_z3_result test_ctx ctx fmtr compare_prop Z3.Solver.SATISFIABLE


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
  let jumps =
    Term.enum blk_t sub
    |> Seq.map ~f:(fun b -> Term.enum jmp_t b)
    |> Seq.concat
  in
  let jmp_spec = fun env post tid jmp ->
    let branch_tid cond =
      Term.tid (Seq.find_exn jumps ~f:(fun j -> Exp.equal (Jmp.cond j) cond)) in
    let branch_cond cond = Pre.bv_to_bool (mk_z3_expr cond env) ctx 1 in
    let branch_pre =
      match Jmp.kind jmp with
      | Goto (Direct tid) -> Option.value (Env.get_precondition env tid) ~default:post
      | _ -> assert false
    in
    let true_constr = Bool.mk_true ctx |> Constr.mk_goal "true" |> Constr.mk_constr in
    let false_constr = Bool.mk_false ctx |> Constr.mk_goal "false" |> Constr.mk_constr in
    if Tid.equal tid (branch_tid cond_x) then
      Some (Constr.mk_ite tid (branch_cond cond_x) branch_pre true_constr)
    else if Tid.equal tid (branch_tid cond_y) then
      Some (Constr.mk_ite tid (branch_cond cond_y) branch_pre true_constr)
    else if Tid.equal tid (branch_tid cond_z) then
      Some (Constr.mk_ite tid (branch_cond cond_z) false_constr true_constr)
    else
      None
  in
  let env = Pre.mk_default_env ctx var_gen ~jmp_spec ~subs:(Seq.singleton sub) in
  let post  = Bool.mk_true ctx
              |> Constr.mk_goal "true"
              |> Constr.mk_constr
  in
  let pre, _ = Pre.visit_sub env post sub in
  let fmtr = format_log_error (Sub.to_string sub) pre post in
  assert_z3_result test_ctx ctx fmtr pre Z3.Solver.SATISFIABLE


let test_exclude_1 (test_ctx : test_ctxt) : unit =
  let ctx = Env.mk_ctx () in
  let solver = Z3.Solver.mk_simple_solver ctx in
  let var = BV.mk_const_s ctx "x" 32 in
  let value = BV.mk_numeral ctx "0" 32 in
  let pre = Bool.mk_eq ctx var value in
  assert_equal ~ctxt:test_ctx ~printer:Z3.Solver.string_of_status
    Z3.Solver.SATISFIABLE (Pre.check solver ctx pre);
  assert_equal ~ctxt:test_ctx ~printer:Z3.Solver.string_of_status
    Z3.Solver.SATISFIABLE (Pre.exclude solver ctx ~var:var ~pre:pre);
  let model = Z3.Solver.get_model solver
              |> Option.value_exn ?here:None ?error:None ?message:None in
  let regs = model
             |> Z3.Model.get_decls
             |> List.map ~f:(fun v -> Z3.FuncDecl.apply v [])
             |> List.filter_map ~f:(fun v -> Z3.Model.eval model v true)
  in
  List.iter regs ~f:(fun v ->
      assert_bool "Variable's value was not properly excluded from the model"
        (not (Expr.equal v value)))


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

  "Compare z := x + y; and x := x + 1; y := y - 1; z := x + y;" >:: test_block_pair_1;
  "Compare z := x; and y := x; z := y;" >:: test_block_pair_2;

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
  "Test call with nested function inlining SAT: \n\
  " >:: test_call_9;
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
  "Read NULL; SAT:\n\
   x = mem[addr];" >:: test_exp_cond_1;
  "Read NULL; UNSAT:\n\
   addr = 0x40000000;\
   x = mem[addr];" >:: test_exp_cond_2;

  "Remove dead assignments" >:: test_sub_pair_1;
  "Remove needed assignments" >:: test_sub_pair_2;
  "Arithmetic across different blocks" >:: test_sub_pair_3;
  "Squashing assignments" >:: test_sub_pair_4;
  "Jump to opposite block" >:: test_sub_pair_5;
  "Same subroutines" >:: test_sub_pair_fun_1;
  "Fun called in modified sub" >:: test_sub_pair_fun_2;
  "Branches with fun calls" >:: test_sub_pair_fun_3;
  "Fun called in branch" >:: test_sub_pair_fun_4;
  "Assert in original, VC in modified UNSAT" >:: test_sub_pair_6;
  "Assert in original, VC in modified SAT" >:: test_sub_pair_7;

  "Signed: Bitwidth 3 -> 8; Value 6 -> -2" >:: test_cast 3 8 6 Bil.SIGNED;
  "Unsigned: Bitwidth 3 -> 8; Value 6 -> 6" >:: test_cast 3 8 6 Bil.UNSIGNED;
  "High: Bitwidth 8 -> 5; Value: 238 -> 29" >:: test_cast 8 5 238 Bil.HIGH;
  "Low: Bitwidth 8 -> 5; Value: 238 -> 14" >:: test_cast 8 5 238 Bil.LOW;

  "Test branches" >:: test_branches_1;

  "Test exclude" >:: test_exclude_1;
]
