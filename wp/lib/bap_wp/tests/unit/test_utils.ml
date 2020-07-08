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
open Bap_wp
open OUnit2

module Pre = Precondition
module Constr = Constraint
module Env = Environment

(* Helper functions to assist in building basic blocks and subroutines *)
let zero : Exp.t = Bil.int @@ Word.zero 32
let one : Exp.t  = Bil.int @@ Word.one 32
let two : Exp.t = Bil.int @@ Word.of_int 2 ~width:32

let i32 (n : int) : Exp.t =
  Bil.int (Word.of_int ~width:32 n)

let i64 (n : int) : Exp.t =
  Bil.int (Word.of_int ~width:64 n)

let x86_64_input_regs : Var.t list =
  Pre.input_regs `x86_64

let mk_def ?tid:(tid = Tid.create ()) (var : var) (exp : exp) (block : Blk.t) : Blk.t =
  Term.append def_t block (Def.create ~tid:tid var exp)

let mk_phi (phi : Phi.t) (block : Blk.t) : Blk.t =
  Term.append phi_t block phi

let mk_jmp ?tid:(tid = Tid.create ()) (dst : Blk.t) (src : Blk.t) : Blk.t =
  Term.append jmp_t src (Jmp.create_goto ~tid:tid (Label.direct (Term.tid dst)))

let mk_call ?tid:(tid = Tid.create ()) (return : label) (target : label) (block : Blk.t)
  : Blk.t =
  let call = Call.create ~return:return ~target:target () in
  Term.append jmp_t block (Jmp.create_call ~tid:tid call)

let mk_int ?tid:(tid = Tid.create ()) (i : int) (return : Blk.t) (block : Blk.t)
  : Blk.t =
  Term.append jmp_t block (Jmp.create_int ~tid:tid i (Term.tid return))

let mk_cond ?tid:(tid = Tid.create ()) (cond : exp) (t : 'a Term.t) (f : 'b Term.t)
    (block : Blk.t) : Blk.t =
  let jmp_true = Jmp.create_goto ~tid:tid ~cond:cond (Label.direct (Term.tid t)) in
  let jmp_false = Jmp.create_goto (Label.direct (Term.tid f)) in
  Term.append jmp_t (Term.append jmp_t block jmp_true) jmp_false

let mk_arg ~intent:(intent : intent) (v : Var.t) : Arg.t =
  Bap.Std.Arg.create ~intent:intent (Var.create ~fresh:true "arg" (Var.typ v)) (Bil.var v)

let mk_sub ?tid:(tid = Tid.create ()) ?args:(args = []) ?name:(name = "")
    (blocks : Blk.t list) : Sub.t =
  let blk_build = Sub.Builder.create ~tid:tid ~name:name () in
  List.iter blocks ~f:(Sub.Builder.add_blk blk_build);
  List.iter args ~f:(Sub.Builder.add_arg blk_build);
  Sub.Builder.result blk_build

let mk_z3_expr (env : Env.t) (e : Exp.t) : Constr.z3_expr =
  let e, _, _ = Pre.exp_to_z3 e env in e

let mk_z3_var (env : Env.t) (v : Var.t) : Constr.z3_expr =
  fst (Env.get_var env v)

let print_z3_model
    ?print_path:(print_path = false) ?print_refuted_goals:(print_refuted_goals = false)
    ~orig:(env1 : Env.t) ~modif:(env2 : Env.t)
    (solver : Z3.Solver.solver) (exp : Z3.Solver.status)
    (real : Z3.Solver.status) (goals : Constr.t) : unit =
  if real = exp || real = Z3.Solver.UNSATISFIABLE then () else
    Output.print_result solver real goals ~print_path ~print_refuted_goals
      ~orig:env1 ~modif:env2

(* Finds a jump in a subroutine given its jump condition. *)
let find_jump (sub : Sub.t) (cond : Exp.t) : Jmp.t =
  let jumps =
    Term.enum blk_t sub
    |> Seq.map ~f:(Term.enum jmp_t)
    |> Seq.concat
  in
  Seq.find_exn jumps ~f:(fun j -> Exp.equal (Jmp.cond j) cond)

(* z3_expr representing a jump being taken. *)
let jump_taken (ctx : Z3.context) : Constr.z3_expr =
  Pre.z3_expr_one ctx 1

(* z3_expr representing a jump not being taken. *)
let jump_not_taken (ctx : Z3.context) : Constr.z3_expr =
  Pre.z3_expr_zero ctx 1

let true_constr (ctx : Z3.context) : Constr.t =
  Z3.Boolean.mk_true ctx
  |> Constr.mk_goal "true"
  |> Constr.mk_constr

let false_constr (ctx : Z3.context) : Constr.t =
  Z3.Boolean.mk_false ctx
  |> Constr.mk_goal "false"
  |> Constr.mk_constr

let test_skip (msg : string) (_ : test_ctxt -> unit) (_ : test_ctxt) : unit =
  skip_if true msg
