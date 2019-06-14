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
module Bool = Z3.Boolean
module Expr = Z3.Expr
module BV = Z3.BitVector

(* To run these tests: `make test.performance` in bap_wp directory *)

let mk_z3_expr e env = let e_val, _, _ = Pre.exp_to_z3 e env in e_val

let format_log_error (body : string) (pre : Env.constr) (post : Env.constr) : string =
  Format.asprintf "Post:\n%a\n\nAnalyzing:\n%sPre:\n%a\n"
    Env.pp_constr post body Env.pp_constr pre

let print_z3_model (ff : Format.formatter) (solver : Z3.Solver.solver)
    (exp : 'a) (real : 'a) : unit =
  if real = exp || real = Z3.Solver.UNSATISFIABLE then () else
    match Z3.Solver.get_model solver with
    | None -> ()
    | Some model -> Format.fprintf ff "\n\nCountermodel:\n%s\n%!" (Z3.Model.to_string model)

let time_z3_result (test_ctx : test_ctxt) (z3_ctx : Z3.context) (formatter : string)
    (pre : Env.constr) (expected : Z3.Solver.status) : float =
  let solver = Z3.Solver.mk_simple_solver z3_ctx in
  let pre = Env.eval_constr z3_ctx pre in
  let is_correct = Bool.mk_implies z3_ctx pre (Bool.mk_false z3_ctx) in
  let start_time = Sys.time () in
  let result = Z3.Solver.check solver [is_correct] in
  let end_time = Sys.time () in
  assert_equal ~ctxt:test_ctx
    ~printer:Z3.Solver.string_of_status
    ~pp_diff:(fun ff (exp, real) ->
        Format.fprintf ff "\n\n%s\n%!" formatter;
        print_z3_model ff solver exp real)
    expected result;
  end_time -. start_time

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

let cond_to_z3 (cond : Exp.t) (env : Env.t) : Env.z3_expr =
  Pre.bv_to_bool (mk_z3_expr cond env) (Env.get_context env) 1

let test_nested_ifs (test_ctx : test_ctxt) : unit =
  let depth = 1000 in
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
            let true_constr = Bool.mk_true ctx |> Env.mk_goal "true" |> Env.mk_constr in
            let false_constr = Bool.mk_false ctx |> Env.mk_goal "false" |> Env.mk_constr in
            if t = tid then begin
              (* The first branch in the seq is the innermost in the nest. *)
              if i = 0 then
                Some (Env.mk_ite tid (cond_to_z3 cond env) false_constr true_constr)
              else
                Some (Env.mk_ite tid (cond_to_z3 cond env) branch_pre true_constr)
            end
            else
              None)
    in
    let env = Pre.mk_default_env ctx var_gen ~jmp_spec ~subs:(Seq.singleton sub) in
    let post  = Bool.mk_true ctx
                |> Env.mk_goal "true"
                |> Env.mk_constr
    in
    let pre, _ = Pre.visit_sub env post sub in
    let fmtr = format_log_error (Sub.to_string sub) pre post in
    time_z3_result test_ctx ctx fmtr pre Z3.Solver.SATISFIABLE
  in

  let time_without_hooks =
    let ctx = Env.mk_ctx () in
    let var_gen = Env.mk_var_gen () in
    let assert_sub, assert_expr = Bil_to_bir.mk_assert_fail () in
    let sub = nest_ifs var_gen depth [Bil.jmp assert_expr] |> bil_to_sub in
    let env = Pre.mk_default_env ctx var_gen ~subs:(Seq.of_list [sub; assert_sub]) in
    let post  = Bool.mk_true ctx
                |> Env.mk_goal "true"
                |> Env.mk_constr
    in
    let pre, _ = Pre.visit_sub env post sub in
    let fmtr = format_log_error (Sub.to_string sub) pre post in
    time_z3_result test_ctx ctx fmtr pre Z3.Solver.SATISFIABLE
  in
  Printf.printf "\nTime with hooks:    %f\nTime without hooks: %f\n%!"
    time_with_hooks time_without_hooks

let suite = [
  "Test branches" >: TestCase (Long, test_nested_ifs);
]
