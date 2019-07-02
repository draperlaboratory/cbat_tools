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
  Format.asprintf "%s: %s%!" g.goal_name (Expr.to_string (Expr.simplify g.goal_val None))

let refuted_goal_to_string (g : goal) (model : Z3.Model.model) : string =
  let buf = Buffer.create 1024 in
  Buffer.add_string buf g.goal_name;
  Buffer.add_string buf ":";
  if Bool.is_eq g.goal_val then begin
    Buffer.add_string buf "\n\tConcrete values: ";
    let args = Expr.get_args g.goal_val in
    List.iteri args ~f:(fun i arg ->
        let value = Option.value_exn (Z3.Model.eval model arg true) in
        if i = 0 then begin
          Buffer.add_string buf (Expr.to_string value);
          Buffer.add_string buf " = "
        end else
          Buffer.add_string buf (Expr.to_string value))
  end;
  Buffer.add_string buf "\n\tZ3 Expression: ";
  Buffer.add_string buf (Expr.to_string (Expr.simplify g.goal_val None));
  Buffer.contents buf

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

let rec to_string (constr : t) : string =
  match constr with
  | Goal g -> goal_to_string g
  | ITE (tid, e, c1, c2) ->
    Format.asprintf "ITE(%s, %s, %s, %s)"
      (Tid.to_string tid) (Expr.to_string e) (to_string c1) (to_string c2)
  | Clause (hyps, concs) ->
    Format.asprintf "%s => %s"
      (List.to_string ~f:to_string hyps) (List.to_string ~f:to_string concs)

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

let mk_constr (g : goal) : t =
  Goal g

let mk_ite (tid : Tid.t) (cond : z3_expr) (c1 : t) (c2 : t) : t =
  ITE (tid, cond, c1, c2)

let mk_clause (hyps: t list) (concs : t list) : t =
  Clause (hyps, concs)

(* This needs to be evaluated in the same context as was used to create the root goals *)
let rec eval (constr : t) (ctx : Z3.context) : z3_expr =
  match constr with
  | Goal { goal_val = v; _ } -> v
  | ITE (_, e, c1, c2) -> Bool.mk_ite ctx e (eval c1 ctx) (eval c2 ctx)
  | Clause (hyps, concs) ->
    let hyps_expr  = hyps |> List.map ~f:(fun h -> eval h ctx) |> Bool.mk_and ctx in
    let concs_expr = concs |> List.map ~f:(fun c -> eval c ctx) |> Bool.mk_and ctx in
    Bool.mk_implies ctx hyps_expr concs_expr

let rec substitute (constr : t) (olds : z3_expr list) (news : z3_expr list) : t =
  match constr with
  | Goal g -> Goal { g with goal_val = Expr.substitute g.goal_val olds news }
  | ITE (tid, e, c1, c2) ->
    let e' = Expr.substitute e olds news in
    let c1' = substitute c1 olds news in
    let c2' = substitute c2 olds news in
    ITE (tid, e', c1', c2')
  | Clause (hyps, concs) ->
    let hyps' = List.map hyps ~f:(fun h -> substitute h olds news) in
    let concs' = List.map concs ~f:(fun c -> substitute c olds news) in
    Clause (hyps', concs')

let substitute_one (constr : t) (old_exp : z3_expr) (new_exp : z3_expr) : t =
  substitute constr [old_exp] [new_exp]

let get_refuted_goals_and_paths (constr : t) (model : Z3.Model.model) (ctx : Z3.context)
  : (goal * path) seq =
  let rec worker (constr : t) (current_path : path) : (goal * path) seq =
    match constr with
    | Goal g ->
      let goal_res = Option.value_exn (Z3.Model.eval model g.goal_val true) in
      if Bool.is_false goal_res then Seq.singleton (g, current_path) else Seq.empty
    | ITE (tid, cond, c1, c2) ->
      let cond_res = Option.value_exn (Z3.Model.eval model cond true) in
      if Bool.is_true cond_res then
        worker c1 (Tid.Map.set current_path ~key:tid ~data:true)
      else
        worker c2 (Tid.Map.set current_path ~key:tid ~data:false)
    | Clause (hyps, concs) ->
      let hyps_false = List.exists hyps
          ~f:(fun h -> Z3.Model.eval model (eval h ctx) true
                       |> Option.value_exn ?here:None ?error:None ?message:None
                       |> Bool.is_false)
      in
      if hyps_false then
        Seq.empty
      else
        List.fold concs ~init:Seq.empty
          ~f:(fun accum c -> Seq.append (worker c current_path) accum)
  in
  worker constr Tid.Map.empty

let get_refuted_goals (constr : t) (model : Z3.Model.model) (ctx : Z3.context)
  : goal seq =
  Seq.map (get_refuted_goals_and_paths constr model ctx) ~f:(fun (g,_) -> g)
