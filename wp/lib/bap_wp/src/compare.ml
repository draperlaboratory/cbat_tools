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

include Self()

module Expr = Z3.Expr
module Bool = Z3.Boolean
module BV = Z3.BitVector
module Env = Environment
module Pre = Precondition
module Constr = Constraint

(* We return an updated pair of environments here, since if we are generating
   fresh variables, we want to keep those same fresh names in the analysis *)
let set_to_eqs (env1 : Env.t) (env2 : Env.t) (vars : Var.Set.t) : Constr.t list * Env.t * Env.t =
  let ctx = Env.get_context env1 in
  let arch = Env.get_arch env1 in
  let module Target = (val target_of_arch arch) in
  (* We keep only the physical variables, since the virtual ones may
     have arbitrary values unrelated to the concrete exectution
     (and in particular be of different types!)
  *)
  let vars = Set.filter vars ~f:(fun v -> Var.is_physical v) in
  Var.Set.fold vars ~init:([], env1, env2)
    ~f:(fun (eqs, env1, env2) v ->
        let var1, env1 = Env.get_var env1 v in
        let var2, env2 = Env.get_var env2 v in
        if Target.CPU.is_mem v then
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
    ~input:(input : Var.Set.t)
    ~output:(output : Var.Set.t)
    ~original:(blk1, env1 : Blk.t * Env.t)
    ~modified:(blk2, env2 : Blk.t * Env.t)
  : Constr.t * Env.t * Env.t =
  (* We only freshen variables in blk2, leaving those of blk1 with
     their original names. *)
  let env2 = Env.set_freshen env2 true in
  let output_eq_list, env1, env2 = set_to_eqs env1 env2 output in
  let output_eq = Constr.mk_clause [] output_eq_list in
  let input_eq_list, env1, env2 = set_to_eqs env1 env2 input in
  let pre1, _ = Pre.visit_block env1 output_eq blk1 in
  let pre2, _ = Pre.visit_block env2 pre1 blk2 in
  let goal = Constr.mk_clause input_eq_list [pre2] in
  goal, env1, env2

(* The type of functions that generate a postcondition or hypothesis for comparative
   analysis. Also updates the environments as needed. *)
type comparator = original:(Sub.t * Env.t) -> modified:(Sub.t * Env.t) ->
  rename_set:Var.Set.t -> Constr.t * Env.t * Env.t

(* A generic function for generating a predicate that compares two subroutines.
   Takes as input a postcondition generator, and a hypothesis generator.
   this could be made even more generic, say by abstracting over the type of terms
   being compared. *)
let compare_subs
    ~postcond:(postcond : comparator)
    ~hyps:(hyps : comparator)
    ~original:(sub1, env1 : Sub.t * Env.t)
    ~modified:(sub2, env2 : Sub.t * Env.t)
  : Constr.t * Env.t * Env.t =
  let env2 = Env.set_freshen env2 true in
  let vars = Var.Set.union
      (Pre.get_vars env1 sub1) (Pre.get_vars env2 sub2) in
  let post, env1, env2 =
    postcond ~original:(sub1, env1) ~modified:(sub2, env2) ~rename_set:vars in
  info "\nPostcondition:\n%s\n%!" (Constr.to_string post);
  let hyps, env1, env2 =
    hyps ~original:(sub1, env1) ~modified:(sub2, env2) ~rename_set:vars in
  info "\nHypotheses:\n%s\n%!" (Constr.to_string hyps);
  let pre_mod, env2 = Pre.visit_sub env2 post sub2 in
  let pre_combined, env1 = Pre.visit_sub env1 pre_mod sub1 in
  let goal = Constr.mk_clause [hyps] [pre_combined] in
  goal, env1, env2

let compare_subs_empty
    ~original:(original : Sub.t * Env.t)
    ~modified:(modified : Sub.t * Env.t)
  : Constr.t * Env.t * Env.t =
  let postcond ~original:(_, env1) ~modified:(_,env2) ~rename_set:_ =
    let ctx = Env.get_context env1 in
    let post = Bool.mk_true ctx |> Constr.mk_goal "true" |> Constr.mk_constr in
    post, env1, env2
  in
  let hyps = postcond in
  compare_subs ~postcond:postcond ~hyps:hyps ~original:original ~modified:modified

let compare_subs_empty_post
    ~input:(_ : Var.Set.t)
    ~original:(original : Sub.t * Env.t)
    ~modified:(modified : Sub.t * Env.t)
  : Constr.t * Env.t * Env.t =
  let postcond ~original:(_, env1) ~modified:(_, env2) ~rename_set:_ =
    let ctx = Env.get_context env1 in
    let post = Bool.mk_true ctx |> Constr.mk_goal "true" |> Constr.mk_constr in
    post, env1, env2
  in
  let hyps ~original:(_, env1) ~modified:(_, env2) ~rename_set =
    let pre_eqs, env1, env2 = set_to_eqs env1 env2 rename_set in
    Constr.mk_clause [] pre_eqs, env1, env2
  in
  compare_subs ~postcond:postcond ~hyps:hyps ~original:original ~modified:modified

(** [mk_smtlib2_compare] builds a constraint out of an smtlib2 string that can be used
    as a comparison predicate between an original and modified binary. *)
let mk_smtlib2_compare (env1 : Env.t) (env2 : Env.t) (smtlib_str : string) : Constr.t =
  let var_map1 = (Env.get_var_map env1) in
  let var_map2 = (Env.get_var_map env2) in
  let smtlib_str = Env.EnvMap.fold var_map1 ~init:smtlib_str
      ~f:(fun ~key:var ~data:z3_var smtlib_str ->
          String.substr_replace_all smtlib_str ~pattern:((Var.name var) ^ "_orig") ~with_:(Z3.Expr.to_string z3_var)
        ) in
  let smtlib_str = Env.EnvMap.fold var_map2 ~init:smtlib_str
      ~f:(fun ~key:var ~data:z3_var smtlib_str ->
          String.substr_replace_all smtlib_str ~pattern:((Var.name var) ^ "_mod") ~with_:(Z3.Expr.to_string z3_var)
        ) in
  info "New smtlib string: %s \n" smtlib_str;
  let declsym1 = Z3_utils.get_decls_and_symbols env1 in
  let declsym2 = Z3_utils.get_decls_and_symbols env2 in
  let declsym = declsym1 @ declsym2 in
  let ctx = Env.get_context env1 in
  Z3_utils.mk_smtlib2 ctx smtlib_str declsym

let compare_subs_eq
    ~input:(input : Var.Set.t)
    ~output:(output : Var.Set.t)
    ~original:(original : Sub.t * Env.t)
    ~modified:(modified : Sub.t * Env.t)
    ~smtlib_post:(smtlib_post : string)
    ~smtlib_hyp:(smtlib_hyp : string)
  : Constr.t * Env.t * Env.t =
  let postcond ~original:(_, env1) ~modified:(_, env2) ~rename_set:_ =
    let post_eqs, env1, env2 = set_to_eqs env1 env2 output in
    let post' = mk_smtlib2_compare env1 env2 smtlib_post in
    Constr.mk_clause [] (post' :: post_eqs), env1, env2
  in
  let hyps ~original:(_, env1) ~modified:(_, env2) ~rename_set:_ =
    let arch = Env.get_arch env1 in
    let module Target = (val target_of_arch arch) in
    let pre_eqs, env1, env2 = set_to_eqs env1 env2 input in
    let init_mem, env1, env2 = init_vars env1 env2 input in
    let sp_range = Pre.set_sp_range env1 in
    let pre' = mk_smtlib2_compare env1 env2 smtlib_hyp in
    Constr.mk_clause [] ([pre'; sp_range] @ init_mem @ pre_eqs), env1, env2
  in
  compare_subs ~postcond:postcond ~hyps:hyps ~original:original ~modified:modified

let compare_subs_fun
    ~original:(original : Sub.t * Env.t)
    ~modified:(modified : Sub.t * Env.t)
  : Constr.t * Env.t * Env.t =
  let mk_is_fun_called env f =
    let ctx = Env.get_context env in
    let f_tid = Env.get_fun_name_tid env f in
    let f_is_called = f_tid |> Option.bind ~f:(Env.get_called env) in
    match f_is_called with
    | None -> Bool.mk_false ctx
    | Some c_f -> Bool.mk_const_s ctx c_f
  in
  let postcond ~original:(_, env1) ~modified:(_, env2) ~rename_set:_ =
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
            clause::goal
          )
    in
    Constr.mk_clause [] no_additional_calls, env1, env2
  in
  let hyps ~original:(_, env1) ~modified:(_, env2) ~rename_set =
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
  compare_subs ~postcond:postcond ~hyps:hyps ~original:original ~modified:modified
