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

module Expr = Z3.Expr
module Bool = Z3.Boolean

type z3_expr = Expr.expr

type path = bool Bap.Std.Tid.Map.t

type goal = { goal_name : string; goal_val : z3_expr }

let goal_to_string (g : goal) : string =
  Format.sprintf "%s: %s%!" g.goal_name (Expr.to_string (Expr.simplify g.goal_val None))

let refuted_goal_to_string (g : goal) (model : Z3.Model.model) : string =
  let buf = Buffer.create 1024 in
  Buffer.add_string buf g.goal_name;
  Buffer.add_string buf ":";
  if Bool.is_eq g.goal_val then begin
    let conc_vals = Buffer.create 1024 in
    let simplified_exprs = Buffer.create 1024 in
    Buffer.add_string conc_vals "\n\tConcrete values: ";
    Buffer.add_string simplified_exprs "\n\tZ3 Expression: ";
    let args = Expr.get_args g.goal_val in
    List.iteri args ~f:(fun i arg ->
        let value = Option.value_exn (Z3.Model.eval model arg true) in
        let simplified = Expr.simplify arg None in
        Buffer.add_string conc_vals (Expr.to_string value);
        Buffer.add_string simplified_exprs (Expr.to_string simplified);
        if i = 0 then begin
          Buffer.add_string conc_vals " = ";
          Buffer.add_string simplified_exprs " = "
        end);
    Buffer.add_buffer buf conc_vals;
    Buffer.add_buffer buf simplified_exprs;
    Buffer.contents buf
  end else begin
    Buffer.add_string buf "\n\tZ3 Expression: ";
    Buffer.add_string buf (Expr.to_string (Expr.simplify g.goal_val None));
    Buffer.contents buf
  end

let mk_goal (name : string) (value : z3_expr) : goal =
  { goal_name = name; goal_val = value }

let get_goal_name (g : goal) : string =
  g.goal_name

let get_goal_val (g : goal) : z3_expr =
  g.goal_val

type t =
  | Goal of goal
  | ITE of Tid.t * z3_expr * t * t
  | Clause of t list * t list
  | Subst of t * z3_expr list * z3_expr list

let rec pp_constr (ch : Format.formatter) (constr : t) : unit =
  match constr with
  | Goal g -> Format.fprintf ch "%s" (goal_to_string g)
  | ITE (tid, e, c1, c2) ->
    Format.fprintf ch "ITE(%s, %s, %a, %a)"
      (Tid.to_string tid) (Expr.to_string e) pp_constr c1 pp_constr c2
  | Clause (hyps, concs) ->
    Format.fprintf ch "(";
    (List.iter hyps ~f:(fun h -> Format.fprintf ch "%a" pp_constr h));
    Format.fprintf ch ") => (";
    (List.iter concs ~f:(fun c -> Format.fprintf ch "%a" pp_constr c));
    Format.fprintf ch ")"
  | Subst (c, olds, news) ->
    Format.fprintf ch "Substitute: %s to %s in %a"
      (List.to_string ~f:Expr.to_string olds) (List.to_string ~f:Expr.to_string news)
      pp_constr c

let to_string (constr : t) : string =
  Format.asprintf "%a" pp_constr constr

let mk_constr (g : goal) : t =
  Goal g

let mk_ite (tid : Tid.t) (cond : z3_expr) (c1 : t) (c2 : t) : t =
  ITE (tid, cond, c1, c2)

let mk_clause (hyps: t list) (concs : t list) : t =
  Clause (hyps, concs)


let rec eval_subst e olds news =
  match olds, news with
  | o :: os, n :: ns ->
    Printf.printf "'%!";
    let e' = Expr.substitute_one e o n in
    eval_subst e' os ns
  | [], [] -> e
  | _, _ -> failwith "Constraint.eval: Substitution with unequal size lists"


let rec eval_aux c olds news ctx =
  match c with
  | Goal { goal_val = v; _ } -> Expr.substitute v olds news
  | ITE (_, e, c1, c2) ->
    let e' = Expr.substitute e olds news in
    Bool.mk_ite ctx e' (eval_aux c1 olds news ctx) (eval_aux c2 olds news ctx)
  | Clause (hyps, concs) ->
    let hyps_expr = List.map hyps ~f:(fun h -> eval_aux h olds news ctx)
                    |> Bool.mk_and ctx in
    let concs_expr = List.map concs ~f:(fun c -> eval_aux c olds news ctx)
                     |> Bool.mk_and ctx in
    Bool.mk_implies ctx hyps_expr concs_expr
  | Subst (c, o, n) ->
    let n' = List.map n ~f:(fun x -> Expr.substitute x olds news) in
    eval_aux c (olds @ o) (news @ n') ctx

(* This needs to be evaluated in the same context as was used to create the root goals *)
let rec eval (constr : t) (ctx : Z3.context) : z3_expr =
  eval_aux constr [] [] ctx

let substitute (constr : t) (olds : z3_expr list) (news : z3_expr list) : t =
  Subst (constr, olds, news)

let substitute_one (constr : t) (old_exp : z3_expr) (new_exp : z3_expr) : t =
  Subst (constr, [old_exp], [new_exp])

let get_refuted_goals_and_paths (constr : t) (model : Z3.Model.model) (ctx : Z3.context)
  : (goal * path) seq =
  let rec worker (constr : t) (current_path : path) (olds : z3_expr list)
      (news : z3_expr list) : (goal * path) seq =
    match constr with
    | Goal g ->
      let goal_val = Expr.substitute g.goal_val olds news in
      let goal_res = Option.value_exn (Z3.Model.eval model goal_val true) in
      if Bool.is_false goal_res then
        Seq.singleton ({g with goal_val = goal_val}, current_path)
      else
        Seq.empty
    | ITE (tid, cond, c1, c2) ->
      let cond_val = Expr.substitute cond olds news in
      let cond_res = Option.value_exn (Z3.Model.eval model cond_val true) in
      if Bool.is_true cond_res then
        worker c1 (Tid.Map.set current_path ~key:tid ~data:true) olds news
      else
        worker c2 (Tid.Map.set current_path ~key:tid ~data:false) olds news
    | Clause (hyps, concs) ->
      let hyps_false = List.exists hyps
          ~f:(fun h -> Z3.Model.eval model (eval_aux h olds news ctx) true
                       |> Option.value_exn ?here:None ?error:None ?message:None
                       |> Bool.is_false)
      in
      if hyps_false then
        Seq.empty
      else
        List.fold concs ~init:Seq.empty
          ~f:(fun accum c -> Seq.append (worker c current_path olds news) accum)
    | Subst (e, o, n) ->
      let n' = List.map n ~f:(fun x -> Expr.substitute x olds news) in
      worker e current_path (olds @ o) (news @ n')
  in
  worker constr Tid.Map.empty [] []

let get_refuted_goals (constr : t) (model : Z3.Model.model) (ctx : Z3.context)
  : goal seq =
  Seq.map (get_refuted_goals_and_paths constr model ctx) ~f:(fun (g,_) -> g)
