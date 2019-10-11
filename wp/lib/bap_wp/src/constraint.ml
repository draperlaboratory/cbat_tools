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
module Model = Z3.Model
module Solver = Z3.Solver

type z3_expr = Expr.expr

type path = bool Jmp.Map.t

type goal = { goal_name : string; goal_val : z3_expr }

let goal_to_string (g : goal) : string =
  Format.sprintf "%s: %s%!" g.goal_name (Expr.to_string (Expr.simplify g.goal_val None))

let pp_path (ch : Format.formatter) (p : path) : unit =
  Format.fprintf ch "Path:\n%!";
  Jmp.Map.iteri p ~f:(fun ~key:jmp ~data:taken ->
      let jmp_str =
        jmp |> Jmp.to_string |> String.substr_replace_first ~pattern:"\n" ~with_:"" in
      let taken_str = if taken then "(taken)" else "(not taken)" in
      let addr_str =
        match Term.get_attr jmp address with
        | None -> "not found"
        | Some addr -> Addr.to_string addr
      in
      Format.fprintf ch "\t%40s %12s (Address: %s)\n%!" jmp_str taken_str addr_str;
    )

let path_to_string (p : path) : string =
  Format.asprintf "%a" pp_path p

let eval_model_exn (model : Model.model) (expr: z3_expr) : z3_expr =
  Model.eval model expr true
  |> Option.value_exn
    ?here:None
    ~error:(Error.of_string "eval_model_exn: Error evaluating expression with model.")
    ~message:(Format.sprintf "Unable to evaluate expr %s with current model."
                (Expr.to_string expr))

let get_model_exn (solver : Solver.solver) : Model.model =
  Solver.get_model solver
  |> Option.value_exn
    ?here:None
    ~error:(Error.of_string "get_model_exn: Error getting the model from the Z3 solver.")
    ~message:(Format.sprintf "Unable to get the model from the Z3 solver : %s"
                (Solver.to_string solver))

let refuted_goal_to_string (g : goal) (model : Model.model) : string =
  let fmt = Format.str_formatter in
  Format.fprintf fmt "%s:" g.goal_name;
  if Bool.is_eq g.goal_val then begin
    let args = Expr.get_args g.goal_val in
    Format.fprintf fmt "\n\tConcrete values: = ";
    List.iter args ~f:(fun arg ->
        let value = eval_model_exn model arg in
        Format.fprintf fmt "%s " (Expr.to_string value));
    Format.fprintf fmt "\n\tZ3 Expression: = ";
    List.iter args ~f:(fun arg ->
        let simplified = Expr.simplify arg None in
        Format.fprintf fmt "%s " (Expr.to_string simplified));
  end else begin
    Format.fprintf fmt "\n\tZ3 Expression: %s"
      (Expr.to_string (Expr.simplify g.goal_val None));
  end;
  Format.flush_str_formatter ()

let mk_goal (name : string) (value : z3_expr) : goal =
  { goal_name = name; goal_val = value }

let get_goal_name (g : goal) : string =
  g.goal_name

let get_goal_val (g : goal) : z3_expr =
  g.goal_val

type t =
  | Goal of goal
  | ITE of Jmp.t * z3_expr * t * t
  | Clause of t list * t list
  | Subst of t * z3_expr list * z3_expr list

let rec pp_constr (ch : Format.formatter) (constr : t) : unit =
  match constr with
  | Goal g -> Format.fprintf ch "%s" (goal_to_string g)
  | ITE (tid, e, c1, c2) ->
    Format.fprintf ch "ITE(%s, %s, %a, %a)"
      (tid |> Term.tid |> Tid.to_string) (Expr.to_string e) pp_constr c1 pp_constr c2
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

let mk_ite (jmp : Jmp.t) (cond : z3_expr) (c1 : t) (c2 : t) : t =
  ITE (jmp, cond, c1, c2)

let mk_clause (hyps: t list) (concs : t list) : t =
  Clause (hyps, concs)

let rec eval_aux (constr : t) (olds : z3_expr list) (news : z3_expr list)
    (ctx : Z3.context) : z3_expr =
  match constr with
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
let eval (constr : t) (ctx : Z3.context) : z3_expr =
  eval_aux constr [] [] ctx

let substitute (constr : t) (olds : z3_expr list) (news : z3_expr list) : t =
  Subst (constr, olds, news)

let substitute_one (constr : t) (old_exp : z3_expr) (new_exp : z3_expr) : t =
  Subst (constr, [old_exp], [new_exp])

let get_refuted_goals_and_paths (constr : t) (solver : Solver.solver)
    (ctx : Z3.context) : (goal * path) seq =
  let model = get_model_exn solver in
  let rec worker (constr : t) (current_path : path) (olds : z3_expr list)
      (news : z3_expr list) : (goal * path) seq =
    match constr with
    | Goal g ->
      let goal_val = Expr.substitute g.goal_val olds news in
      let goal_res = eval_model_exn model goal_val in
      begin
        match Solver.check solver [goal_res] with
        | Solver.SATISFIABLE -> Seq.empty
        | Solver.UNSATISFIABLE ->
          Seq.singleton ({g with goal_val = goal_val}, current_path)
        | Solver.UNKNOWN ->
          failwith (Format.sprintf "get_refuted_goals: Unable to resolve %s" g.goal_name)
      end
    | ITE (jmp, cond, c1, c2) ->
      let cond_val = Expr.substitute cond olds news in
      let cond_res = eval_model_exn model cond_val in
      begin
        match Solver.check solver [cond_res] with
        | Solver.SATISFIABLE ->
          worker c1 (Jmp.Map.set current_path ~key:jmp ~data:true) olds news
        | Solver.UNSATISFIABLE ->
          worker c2 (Jmp.Map.set current_path ~key:jmp ~data:false) olds news
        | Solver.UNKNOWN ->
          failwith (Format.sprintf "get_refuted_goals: Unable to resolve branch \
                                    condition at %s" (jmp |> Term.tid |> Tid.to_string))
      end
    | Clause (hyps, concs) ->
      let hyps_false =
        let hyp_vals =
          List.map hyps ~f:(fun h -> eval_model_exn model (eval_aux h olds news ctx)) in
        match Solver.check solver hyp_vals with
        | Solver.SATISFIABLE -> false
        | Solver.UNSATISFIABLE -> true
        | Solver.UNKNOWN ->
          failwith "get_refuted_goals: Unable to resolve value of hypothesis"
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
  worker constr Jmp.Map.empty [] []

let get_refuted_goals (constr : t) (solver : Solver.solver) (ctx : Z3.context)
  : goal seq =
  Seq.map (get_refuted_goals_and_paths constr solver ctx) ~f:(fun (g,_) -> g)
