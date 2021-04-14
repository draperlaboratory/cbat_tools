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
module Env = Environment
module Constr = Constraint
module Bool = Z3.Boolean
module Expr = Z3.Expr
module BV = Z3.BitVector
module Solver = Z3.Solver

(* To run these tests: `make test.performance` in bap_wp directory *)

let mk_z3_expr e env = let e_val, _, _ = Pre.exp_to_z3 e env in e_val

let hook_slowdown_msg (time1 : float) (time2 : float) : string =
  Format.sprintf "Time with hooks is slower than time without hooks:\n \
                  Time with hooks:    %f\nTime without hooks: %f\n%!" time1 time2

let z3_overtime_msg (threshold : float) (actual : float) : string =
  Format.sprintf "Running Z3 took longer than expected:\n \
                  Expected: %fs\nActual:   %fs" threshold actual

let no_model (s1 : Solver.status) (s2 : Solver.status) : bool =
  match s1, s2 with
  | Solver.SATISFIABLE, Solver.SATISFIABLE
  | Solver.UNKNOWN, Solver.UNKNOWN
  | Solver.UNSATISFIABLE, _ -> true
  | _, _ -> false

let print_z3_model (ff : Format.formatter) (solver : Solver.solver)
    (exp : 'a) (real : 'a) : unit =
  if no_model real exp then () else
    match Solver.get_model solver with
    | None -> ()
    | Some model -> Format.fprintf ff "\n\nCountermodel:\n%s\n%!" (Z3.Model.to_string model)

let time_z3_result (test_ctx : test_ctxt) (z3_ctx : Z3.context) (body : Sub.t)
    (post : Constr.t) (pre : Constr.t) (expected : Solver.status) (threshold : float)
  : float =
  let solver = Solver.mk_simple_solver z3_ctx in
  let start_time = Sys.time () in
  let result = Pre.check solver z3_ctx pre in
  let end_time = Sys.time () in
  assert_equal ~ctxt:test_ctx
    ~printer:Solver.string_of_status
    ~pp_diff:(fun ff (exp, real) ->
        Format.fprintf ff "\n\nPost:\n%a\n\nAnalyzing:\n%sPre:\n%a\n\n%!"
          (Constr.pp ()) post (Sub.to_string body) (Constr.pp ()) pre;
        print_z3_model ff solver exp real)
    expected result;
  let time = end_time -. start_time in
  assert_bool (z3_overtime_msg threshold time) Float.(time <=. threshold);
  time

let i32 n = Bil.int (Word.of_int ~width:32 n)

let rec nest_ifs (var_gen : Env.var_gen) (level : int) (deepest_stmt : stmt list)
  : stmt list =
  if level = 0 then
    deepest_stmt
  else begin
    let v = Var.create (Env.get_fresh var_gen) reg32_t in
    let cond = Bil.(var v = i32 level) in
    let stmt = nest_ifs var_gen (level - 1) deepest_stmt in
    [ Bil.if_ (cond)
        stmt
        []
    ]
  end

let branch_info (sub : Sub.t) : (Tid.t * Exp.t) Seq.t =
  let jumps =
    Term.enum blk_t sub
    |> Seq.map ~f:(fun b -> Term.enum jmp_t b)
    |> Seq.concat
  in
  let conditional_jumps = Seq.filter jumps
      ~f:(fun j -> not (Exp.equal (Jmp.cond j) (Bil.int @@ Word.one 1))) in
  Seq.map conditional_jumps ~f:(fun j -> (Term.tid j, Jmp.cond j))

let cond_to_z3 (cond : Exp.t) (env : Env.t) : Constr.z3_expr =
  Pre.bv_to_bool (mk_z3_expr cond env) (Env.get_context env) 1

let test_nested_ifs (threshold : float) (test_ctx : test_ctxt) : unit =
  let depth = 200 in
  let time_with_hooks =
    let ctx = Env.mk_ctx () in
    let var_gen = Env.mk_var_gen () in
    let sub = nest_ifs var_gen depth [] |> bil_to_sub in
    let jmp_spec = fun env post tid jmp ->
      let branch_pre =
        match Jmp.kind jmp with
        | Goto (Direct tid) -> Option.value (Env.get_precondition env tid) ~default:post
        | _ -> assert false
      in
      Seq.find_mapi (branch_info sub)
        ~f:(fun i (t, cond) ->
            let true_constr = Bool.mk_true ctx
                              |> Constr.mk_goal "true"
                              |> Constr.mk_constr
            in
            let false_constr = Bool.mk_false ctx
                               |> Constr.mk_goal "false"
                               |> Constr.mk_constr
            in
            if Tid.equal t tid then begin
              (* The first branch in the seq is the innermost in the nest. *)
              if i = 0 then
                Some (Constr.mk_ite jmp (cond_to_z3 cond env) false_constr true_constr, env)
              else
                Some (Constr.mk_ite jmp (cond_to_z3 cond env) branch_pre true_constr, env)
            end
            else
              None)
    in
    let env = Pre.mk_env ctx var_gen ~jmp_spec ~subs:(Seq.singleton sub) in
    let post  = Bool.mk_true ctx
                |> Constr.mk_goal "true"
                |> Constr.mk_constr
    in
    let pre, _ = Pre.visit_sub env post sub in
    time_z3_result test_ctx ctx sub post pre Solver.SATISFIABLE threshold
  in

  let time_without_hooks =
    let ctx = Env.mk_ctx () in
    let var_gen = Env.mk_var_gen () in
    let assert_sub, assert_expr = Bil_to_bir.mk_assert_fail () in
    let sub = nest_ifs var_gen depth [Bil.jmp assert_expr] |> bil_to_sub in
    let env = Pre.mk_env ctx var_gen ~subs:(Seq.of_list [sub; assert_sub])
        ~specs:[Pre.spec_verifier_error] in
    let post  = Bool.mk_true ctx
                |> Constr.mk_goal "true"
                |> Constr.mk_constr
    in
    let pre, _ = Pre.visit_sub env post sub in
    time_z3_result test_ctx ctx sub post pre Solver.SATISFIABLE threshold
  in
  assert_bool (hook_slowdown_msg time_with_hooks time_without_hooks)
    Float.(time_with_hooks <. time_without_hooks)

let suite = [
  "Test branches" >: TestCase (Long, test_nested_ifs 10.0);
]
