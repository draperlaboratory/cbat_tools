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

open !Core
open Bap.Std

include Self()

module Expr = Z3.Expr
module Bool = Z3.Boolean
module BV = Z3.BitVector
module Env = Environment
module Pre = Precondition
module Constr = Constraint

type 'a code =
  {
    prog : 'a term;
    env : Env.t;
    mem : value memmap;
    code_addrs : Utils.Code_addrs.t;
  }


(* We return an updated pair of environments here, since if we are generating
   fresh variables, we want to keep those same fresh names in the analysis *)
let set_to_eqs (env1 : Env.t) (env2 : Env.t) (vars : Var.Set.t) : Constr.t list * Env.t * Env.t =
  let ctx = Env.get_context env1 in
  (* We keep only the physical variables, since the virtual ones may
     have arbitrary values unrelated to the concrete exectution
     (and in particular be of different types!)
  *)
  let vars = Set.filter vars ~f:Var.is_physical in
  Var.Set.fold vars ~init:([], env1, env2)
    ~f:(fun (eqs, env1, env2) v ->
        let var1, env1 = Env.get_var env1 v in
        let var2, env2 = Env.get_var env2 v in
        if Var.(Env.get_mem env1 = v) then
          eqs, env1, env2
        else
          let eq = Bool.mk_eq ctx var1 var2
                   |> Constr.mk_goal
                     (Format.sprintf "%s = %s" (Expr.to_string var1) (Expr.to_string var2))
                   |> Constr.mk_constr
          in (eq::eqs, env1, env2)
      )

(* Adds the hypothesis: [var == init_var] for each variable in the set. *)
let init_vars (env1 : Env.t) (env2 : Env.t) (vars : Var.Set.t)
  : Constr.t list * Env.t * Env.t =
  let vars = Set.filter vars ~f:Var.is_physical in
  let inits1, env1 = Pre.init_vars vars env1 in
  let inits2, env2 = Pre.init_vars vars env2 in
  (inits1 @ inits2), env1, env2

let compare_blocks
    ~pre_regs:(pre_regs : Var.Set.t)
    ~post_regs:(post_regs : Var.Set.t)
    ~original:({ prog=blk1; env=env1; _ } : blk code)
    ~modified:({ prog=blk2; env=env2; _ } : blk code)
    ~smtlib_post:(smtlib_post : string)
    ~smtlib_hyp:(smtlib_hyp : string)
  : Constr.t * Env.t * Env.t =
  (* We only freshen variables in blk2, leaving those of blk1 with
     their original names. *)
  let env2 = Env.set_freshen env2 true in
  let post_eq_list, env1, env2 = set_to_eqs env1 env2 post_regs in
  let smtlib_post =
    Z3_utils.mk_smtlib2_compare ~name:(Some "Custom postcondition")
      env1 env2 smtlib_post in
  let output_eq = Constr.mk_clause [] (smtlib_post :: post_eq_list) in
  let pre_eq_list, env1, env2 = set_to_eqs env1 env2 pre_regs in
  let smtlib_hyp =
    Z3_utils.mk_smtlib2_compare ~name:(Some "Custom precondition")
      env1 env2 smtlib_hyp in
  let pre1, _ = Pre.visit_block env1 output_eq blk1 in
  let pre2, _ = Pre.visit_block env2 pre1 blk2 in
  let goal = Constr.mk_clause (smtlib_hyp :: pre_eq_list) [pre2] in
  goal, env1, env2

(* The type of functions that generate a postcondition or hypothesis for comparative
   analysis. Also updates the environments as needed. *)
type comparator = original:sub code -> modified:sub code ->
  rename_set:Var.Set.t -> Constr.t * Env.t * Env.t

let fold_comparators
    ~original:(code1 : sub code)
    ~modified:(code2 : sub code)
    ~rename_set:(vars : Var.Set.t)
    (comparators : comparator list)
  : Constr.t * Env.t * Env.t =
  let env1 = code1.env in
  let env2 = code2.env in
  let ctx = Env.get_context env1 in
  let constrs, env1, env2 =
    List.fold comparators ~init:([], env1, env2)
      ~f:(fun (comps, env1, env2) comp ->
          let c, env1, env2 =
            comp
              ~original:{ code1 with env=env1 }
              ~modified:{ code2 with env=env2 }
              ~rename_set:vars
          in
          (* We are not adding the trivial constraints to prevent blow up in
             the final precondition. *)
          if Bool.is_true (Constr.eval c ctx) then
            comps, env1, env2
          else
            c :: comps, env1, env2)
  in
  Constr.mk_clause [] constrs, env1, env2

(* A generic function for generating a predicate that compares two subroutines.
   Takes as input a postcondition generator, and a hypothesis generator.
   this could be made even more generic, say by abstracting over the type of terms
   being compared. *)
let compare_subs
    ~postconds:(postconds : comparator list)
    ~hyps:(hyps : comparator list)
    ~original:(code1 : sub code)
    ~modified:(code2 : sub code)
  : Constr.t * Env.t * Env.t =
  let env2 = Env.set_freshen code2.env true in
  let code2 = { code2 with env = env2 } in
  let vars = Var.Set.union
      (Pre.get_vars code1.env code1.prog) (Pre.get_vars code2.env code2.prog) in
  let post, env1, env2 =
    fold_comparators postconds
      ~original:code1
      ~modified:code2
      ~rename_set:vars
  in
  info "\nPostcondition:\n%s\n%!" (Constr.to_string post);
  let hyps, env1, env2 =
    (* We will always generate Z3 variables representing the initial value of
       registers in the subroutine. *)
    let init_vars ~original:code1 ~modified:code2 ~rename_set:vars =
      let vars, env1, env2 = init_vars code1.env code2.env vars in
      Constr.mk_clause [] vars, env1, env2
    in
    fold_comparators (init_vars :: hyps)
      ~original:{ code1 with env=env1 }
      ~modified:{ code2 with env=env2 }
      ~rename_set:vars
  in
  info "\nHypotheses:\n%s\n%!" (Constr.to_string hyps);
  let pre_mod, env2 = Pre.visit_sub env2 post code2.prog in
  let pre_combined, env1 = Pre.visit_sub env1 pre_mod code1.prog in
  let goal = Constr.mk_clause [hyps] [pre_combined] in
  goal, env1, env2

let compare_subs_empty : comparator * comparator =
  let postcond ~original:{ env = env1; _ } ~modified:{ env = env2; _ } ~rename_set:_ =
    let ctx = Env.get_context env1 in
    let post = Constr.trivial ctx in
    post, env1, env2
  in
  let hyps = postcond in
  postcond, hyps

let compare_subs_empty_post : comparator * comparator =
  let postcond ~original:{ env = env1; _ } ~modified:{ env = env2; _ } ~rename_set:_ =
    let ctx = Env.get_context env1 in
    let post = Constr.trivial ctx in
    post, env1, env2
  in
  let hyps ~original:{ env = env1; _ } ~modified:{ env = env2; _ } ~rename_set =
    let pre_eqs, env1, env2 = set_to_eqs env1 env2 rename_set in
    Constr.mk_clause [] pre_eqs, env1, env2
  in
  postcond, hyps

let compare_subs_sp : comparator * comparator =
  let postcond ~original:{ env = env1; _ } ~modified:{ env = env2; _ } ~rename_set:_ =
    let ctx = Env.get_context env1 in
    let post = Constr.trivial ctx in
    post, env1, env2
  in
  let hyps ~original:{ env = env1; _ } ~modified:{ env = env2; _ } ~rename_set =
    let sp_range = Pre.set_sp_range env1 in
    let pre_eqs, env1, env2 = set_to_eqs env1 env2 rename_set in
    Constr.mk_clause [] (sp_range :: pre_eqs), env1, env2
  in
  postcond, hyps

let compare_subs_smtlib
    ~smtlib_post:(smtlib_post : string)
    ~smtlib_hyp:(smtlib_hyp : string)
  : comparator * comparator =
  let postcond ~original:{ env = env1; _ } ~modified:{ env = env2; _ } ~rename_set:_ =
    Z3_utils.mk_smtlib2_compare env1 env2 smtlib_post, env1, env2
  in
  let hyps ~original:{ env = env1; _ } ~modified:{ env = env2; _ } ~rename_set =
    let smtlib = Z3_utils.mk_smtlib2_compare env1 env2 smtlib_hyp in
    let pre_eqs, env1, env2 = set_to_eqs env1 env2 rename_set in
    Constr.mk_clause [] (smtlib :: pre_eqs), env1, env2
  in
  postcond, hyps

let compare_subs_eq
    ~pre_regs:(pre_regs : Var.Set.t)
    ~post_regs:(post_regs : Var.Set.t)
  : comparator * comparator =
  let postcond ~original:{ env = env1; _ } ~modified:{ env = env2; _ } ~rename_set:_ =
    let post_eqs, env1, env2 = set_to_eqs env1 env2 post_regs in
    Constr.mk_clause [] post_eqs, env1, env2
  in
  let hyps ~original:{ env = env1; _ } ~modified:{ env = env2; _ } ~rename_set:_ =
    let pre_eqs, env1, env2 = set_to_eqs env1 env2 pre_regs in
    Constr.mk_clause [] pre_eqs, env1, env2
  in
  postcond, hyps

let compare_subs_constraints
    ~pre_conds:(pre_conds : Constr.t)
    ~post_conds:(post_conds : Constr.t)
  : comparator * comparator =
  let postcond ~original:{ env = env1; _ } ~modified:{ env = env2; _ } ~rename_set:_ =
    Constr.mk_clause [] [post_conds], env1, env2
  in
  let hyps ~original:{ env = env1; _ } ~modified:{ env = env2; _ } ~rename_set =
    let pre_eqs, env1, env2 = set_to_eqs env1 env2 rename_set in
    Constr.mk_clause [] (pre_conds :: pre_eqs), env1, env2
  in
  postcond, hyps


let compare_subs_fun : comparator * comparator =
  let mk_is_fun_called env f =
    let ctx = Env.get_context env in
    let f_tid = Env.get_fun_name_tid env f in
    let f_is_called = f_tid |> Option.bind ~f:(Env.get_called env) in
    match f_is_called with
    | None -> Bool.mk_false ctx
    | Some c_f -> Bool.mk_const_s ctx c_f
  in
  let postcond ~original:{ env = env1; _ } ~modified:{ env = env2; _ } ~rename_set:_ =
    let ctx = Env.get_context env1 in
    (* Create the goal /\_f Called_f_original => Called_f_modified *)
    let no_additional_calls =
      Env.fold_fun_tids env1 ~init:[]
        ~f:(fun ~key:f ~data:_ goal ->
            let f_not_called_original =
              (* TODO: update the context with this? *)
              Bool.mk_not ctx (mk_is_fun_called env1 f)
              |> Constr.mk_goal (Format.sprintf "%s not called in original" f)
              |> Constr.mk_constr
            in
            let f_not_called_modified =
              (* TODO: same thing? *)
              Bool.mk_not ctx (mk_is_fun_called env2 f)
              |> Constr.mk_goal (Format.sprintf "%s not called in modified" f)
              |> Constr.mk_constr
            in
            let clause = Constr.mk_clause [f_not_called_original] [f_not_called_modified] in
            clause :: goal
          )
    in
    Constr.mk_clause [] no_additional_calls, env1, env2
  in
  let hyps ~original:{ env = env1; _ } ~modified:{ env = env2; _ } ~rename_set =
    let ctx = Env.get_context env1 in
    (* Create the hypothesis /\_f !Called_f_modified *)
    let modified_not_called =
      Env.fold_fun_tids env2 ~init:[]
        ~f:(fun ~key:f ~data:_ hyp ->
            let f_not_called_modified =
              Bool.mk_not ctx (mk_is_fun_called env2 f)
              |> Constr.mk_goal (Format.sprintf "%s not called in modified" f)
              |> Constr.mk_constr
            in
            f_not_called_modified::hyp
          )
    in
    let eqs, env1, env2 = set_to_eqs env1 env2 rename_set in
    Constr.mk_clause [] (eqs @ modified_not_called), env1, env2
  in
  postcond, hyps

let compare_subs_mem_eq : comparator * comparator =
  let postcond ~original:{ env = env1; _ } ~modified:{ env = env2; _ } ~rename_set:_ =
    let ctx = Env.get_context env1 in
    let post = Constr.trivial ctx in
    post, env1, env2
  in
  let hyps ~original:{ env = env1; _ } ~modified:{ env = env2; _ } ~rename_set =
    let ctx = Env.get_context env1 in
    let mem1, env1 = Env.get_var env1 (Env.get_mem env1) in
    let mem2, env2 = Env.get_var env2 (Env.get_mem env2) in
    let mem_eq =
      Bool.mk_eq ctx mem1 mem2
      |> Constr.mk_goal "mem_orig = mem_mod"
      |> Constr.mk_constr
    in
    let pre_eqs, env1, env2 = set_to_eqs env1 env2 rename_set in
    Constr.mk_clause [] (mem_eq :: pre_eqs), env1, env2
  in
  postcond, hyps

let compare_subs_mem_init : comparator * comparator =
  let postcond ~original ~modified ~rename_set:_ =
    let ctx = Env.get_context original.env in
    let post = Constr.trivial ctx in
    post, original.env, modified.env
  in
  let hyps ~original ~modified ~rename_set:_ =
    let mem_orig, env1 =
      Pre.init_mem original.env original.mem original.code_addrs in
    let mem_mod, env2 =
      Pre.init_mem modified.env modified.mem modified.code_addrs in
    let pre = Constr.mk_clause [] (mem_orig @ mem_mod) in
    pre, env1, env2
  in
  postcond, hyps
