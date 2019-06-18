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
module Env = Environment
module Pre = Precondition
module Constr = Constraint


type rename_map = var Var.Map.t

let mk_rename_map (vars : Var.Set.t) : rename_map =
  let freshen v = Var.create ~is_virtual:(Var.is_virtual v) ~fresh:true
      (Var.name v) (Var.typ v) in
  Var.Set.fold vars ~init:Var.Map.empty
    ~f:(fun vm v -> Var.Map.set vm ~key:v ~data:(freshen v))

let freshen_block (rename_map : var Var.Map.t) (blk : Blk.t) : Blk.t =
  (* Rename all the variables in blk *)
  let subst_exp m e =
    let vs = Var.Map.keys m in
    List.fold vs ~init:e
      ~f:(fun e v -> Exp.substitute (Bil.var v) (Var.Map.find m v |>
                                                 Option.value ~default:v
                                                 |> Bil.var)
             e)
  in
  let subst_exps m b = Blk.map_exp b ~f:(fun e -> subst_exp m e) in
  let subst_vars m b = Blk.map_lhs b ~f:(fun v -> Var.Map.find m v |> Option.value ~default:v) in
  let subst_all m b = b |> subst_exps m |> subst_vars m in
  blk |> subst_all rename_map

let freshen_sub (rename_map : var Var.Map.t) (sub : Sub.t) : Sub.t =
  Term.map blk_t sub ~f:(freshen_block rename_map)

let map_to_eqs (ctx : Z3.context) (m : var Var.Map.t) : Constr.t list =
  let pairs = Var.Map.to_alist m in
  List.map pairs ~f:(fun (v1, v2) ->
      let var1 = Pre.var_to_z3 ctx v1 in
      let var2 = Pre.var_to_z3 ctx v2 in
      Bool.mk_eq ctx var1 var2
      |> Constr.mk_goal (Format.sprintf "%s = %s" (Expr.to_string var1) (Expr.to_string var2))
      |> Constr.mk_constr)

let compare_blocks
    ~input:(input : Var.Set.t)
    ~output:(output : Var.Set.t)
    ~original:(blk1, env1 : Blk.t * Env.t)
    ~modified:(blk2, env2 : Blk.t * Env.t)
  : Constr.t * Env.t =
  let ctx = Env.get_context env1 in
  let rename_map = mk_rename_map (Var.Set.union input output) in
  let blk2 = freshen_block rename_map blk2 in
  let input_map = Var.Map.filteri rename_map
      ~f:(fun ~key:v ~data:_ -> Var.Set.mem input v) in
  let output_map = Var.Map.filteri rename_map
      ~f:(fun ~key:v ~data:_ -> Var.Set.mem output v) in
  let output_eq = Constr.mk_clause [] (map_to_eqs ctx output_map) in
  let input_eq = map_to_eqs ctx input_map in
  let pre1, _ = Pre.visit_block env1 output_eq blk1 in
  let pre2, _ = Pre.visit_block env2 pre1 blk2 in
  let goal = Constr.mk_clause input_eq [pre2] in
  goal, env2

(* The type of functions that generate a postcondition or hypothesis for comparative
   analysis. *)
type comparator = original:(Sub.t * Env.t) -> modified:(Sub.t * Env.t) ->
  rename_map:(var Var.Map.t) -> Constr.t

(* A generic function for generating a predicate that compares two subroutines.
   Takes as input a postcondition generator, and a hypothesis generator.
   this could be made even more generic, say by abstracting over the type of terms
   being compared. *)
let compare_subs
    ~postcond:(postcond : comparator)
    ~hyps:(hyps : comparator)
    ~original:(sub1, env1 : Sub.t * Env.t)
    ~modified:(sub2, env2 : Sub.t * Env.t)
  : Constr.t * Env.t =
  let vars = Var.Set.union
      (Pre.get_vars sub1) (Pre.get_vars sub2) in
  let rename_map = mk_rename_map vars in
  let sub2 = freshen_sub rename_map sub2 in
  let post = postcond ~original:(sub1, env1) ~modified:(sub2, env2) ~rename_map:rename_map in
  info "\nPostcondition:\n%s\n%!" (Constr.to_string post);
  let pre_mod, _ = Pre.visit_sub env2 post sub2 in
  let pre_combined, _ = Pre.visit_sub env1 pre_mod sub1 in
  let hyps = hyps ~original:(sub1, env1) ~modified:(sub2, env2) ~rename_map:rename_map in
  info "\nHypotheses:\n%s\n%!" (Constr.to_string hyps);
  let goal = Constr.mk_clause [hyps] [pre_combined] in
  goal, env2

let compare_subs_empty
    ~original:(original : Sub.t * Env.t)
    ~modified:(modified : Sub.t * Env.t)
  : Constr.t * Env.t =
  let postcond ~original:(_, env) ~modified:_ ~rename_map:_ =
    let ctx = Env.get_context env in
    Bool.mk_true ctx |> Constr.mk_goal "true" |> Constr.mk_constr
  in
  let hyps = postcond in
  compare_subs ~postcond:postcond ~hyps:hyps ~original:original ~modified:modified

let compare_subs_empty_post
    ~input:(input : Var.Set.t)
    ~original:(original : Sub.t * Env.t)
    ~modified:(modified : Sub.t * Env.t)
  : Constr.t * Env.t =
  let postcond ~original:(_, env) ~modified:_ ~rename_map:_ =
    let ctx = Env.get_context env in
    Bool.mk_true ctx |> Constr.mk_goal "true" |> Constr.mk_constr
  in
  let hyps ~original:(_, env) ~modified:_ ~rename_map =
    let ctx = Env.get_context env in
    let input_map = Var.Map.filteri rename_map
        ~f:(fun ~key:v ~data:_ -> Var.Set.mem input v)
    in
    Constr.mk_clause [] (map_to_eqs ctx input_map)
  in
  compare_subs ~postcond:postcond ~hyps:hyps ~original:original ~modified:modified

let compare_subs_eq
    ~input:(input : Var.Set.t)
    ~output:(output : Var.Set.t)
    ~original:(original : Sub.t * Env.t)
    ~modified:(modified : Sub.t * Env.t)
  : Constr.t * Env.t =
  let postcond ~original:(_, env) ~modified:_ ~rename_map =
    let ctx = Env.get_context env in
    let output_map = Var.Map.filteri rename_map
        ~f:(fun ~key:v ~data:_ -> Var.Set.mem output v)
    in
    Constr.mk_clause [] (map_to_eqs ctx output_map)
  in
  let hyps ~original:(_, env) ~modified:_ ~rename_map =
    let ctx = Env.get_context env in
    let input_map = Var.Map.filteri rename_map
        ~f:(fun ~key:v ~data:_ -> Var.Set.mem input v)
    in
    Constr.mk_clause [] (map_to_eqs ctx input_map)
  in
  compare_subs ~postcond:postcond ~hyps:hyps ~original:original ~modified:modified

let compare_subs_fun
    ~original:(original : Sub.t * Env.t)
    ~modified:(modified : Sub.t * Env.t)
  : Constr.t * Env.t =
  let mk_is_fun_called env f =
    let ctx = Env.get_context env in
    let f_tid = Env.get_fun_name_tid env f in
    let f_is_called = f_tid |> Option.bind ~f:(Env.get_called env) in
    match f_is_called with
    | None -> Bool.mk_false ctx
    | Some c_f -> Bool.mk_const_s ctx c_f
  in
  let postcond ~original:(_, env1) ~modified:(_, env2) ~rename_map:_ =
    let ctx = Env.get_context env1 in
    (* Create the goal /\_f Called_f_original => Called_f_modified *)
    let no_additional_calls =
      Env.fold_fun_tids env1 ~init:[]
        ~f:(fun ~key:f ~data:_ goal ->
            let f_not_called_original =
              Bool.mk_not ctx (mk_is_fun_called env1 f)
              |> Constr.mk_goal (Format.sprintf "%s not called in original" f)
              |> Constr.mk_constr
            in
            let f_not_called_modified =
              Bool.mk_not ctx (mk_is_fun_called env2 f)
              |> Constr.mk_goal (Format.sprintf "%s not called in modified" f)
              |> Constr.mk_constr
            in
            let clause = Constr.mk_clause [f_not_called_original] [f_not_called_modified] in
            clause::goal
          )
    in
    Constr.mk_clause [] no_additional_calls
  in
  let hyps ~original:(_, env1) ~modified:(_, env2) ~rename_map =
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
    let eqs = map_to_eqs ctx rename_map in
    Constr.mk_clause [] (eqs @ modified_not_called)
  in
  compare_subs ~postcond:postcond ~hyps:hyps ~original:original ~modified:modified
