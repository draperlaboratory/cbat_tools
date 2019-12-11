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

(* A map containing pairs of a register and its value at specific jumps in the program. *)
type reg_map = (z3_expr * z3_expr) list Jmp.Map.t

type goal = { goal_name : string; goal_val : z3_expr }

type refuted_goal = { goal : goal; path : path; reg_map : reg_map }

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

let goal_to_string (g : goal) : string =
  Format.sprintf "%s: %s%!" g.goal_name (Expr.to_string (Expr.simplify g.goal_val None))

let format_values (fmt : Format.formatter) (vals : (string * z3_expr) list) : unit =
  let max_str_length =
    vals
    |> List.map ~f:(fun (v, _) -> String.length v)
    |> List.max_elt ~compare:Int.compare
  in
  match max_str_length with
  | None -> ()
  | Some length ->
    List.iter vals
      ~f:(fun (var, value) ->
          let pad_size = length - (String.length var) + 1 in
          let pad = String.make pad_size ' ' in
          Format.fprintf fmt
            "\t%s%s|->  @[%s@]@\n" var pad (Expr.to_string value))

let format_registers (fmt : Format.formatter) (regs : reg_map) (jmp : Jmp.t)
    (var_map : z3_expr Var.Map.t) : unit =
  match Jmp.Map.find regs jmp with
  | None -> ()
  | Some regs ->
    let reg_vals = Var.Map.fold var_map ~init:[]
        ~f:(fun ~key ~data pairs ->
            match List.find regs ~f:(fun (r, _) -> Expr.equal data r) with
            | None -> pairs
            | Some (_, value) -> (Var.to_string key, value) :: pairs)
    in
    format_values fmt reg_vals;
    Format.fprintf fmt "\n%!"

let format_path (fmt : Format.formatter) (p : path) (regs : reg_map)
    (var_map : z3_expr Var.Map.t) : unit =
  Format.fprintf fmt "\n\tPath:\n%!";
  Jmp.Map.iteri p
    ~f:(fun ~key:jmp ~data:taken ->
        let jmp_str =
          jmp
          |> Jmp.to_string
          |> String.substr_replace_first ~pattern:"\n" ~with_:"" in
        let taken_str = if taken then "(taken)" else "(not taken)" in
        begin
          match Term.get_attr jmp address with
          | None -> Format.fprintf fmt "\t%s %s (Address not found)\n%!" jmp_str taken_str
          | Some addr ->
            Format.fprintf fmt "\t%s %s (Address: %s)\n%!"
              jmp_str taken_str (Addr.to_string addr)
        end;
        format_registers fmt regs jmp var_map)

let path_to_string (p : path) : string =
  let fmt = Format.str_formatter in
  format_path fmt p Jmp.Map.empty Var.Map.empty;
  Format.flush_str_formatter ()

let format_goal (fmt : Format.formatter) (g : goal) (model : Model.model) : unit =
  Format.fprintf fmt "%s:" g.goal_name;
  if Bool.is_eq g.goal_val then
    begin
      let args = Expr.get_args g.goal_val in
      Format.fprintf fmt "\n\tConcrete values: = ";
      List.iter args ~f:(fun arg ->
          let value = eval_model_exn model arg in
          Format.fprintf fmt "%s " (Expr.to_string value));
      Format.fprintf fmt "\n\tZ3 Expression: = ";
      List.iter args ~f:(fun arg ->
          let simplified = Expr.simplify arg None in
          Format.fprintf fmt "%s " (Expr.to_string simplified));
    end
  else
    Format.fprintf fmt "\n\tZ3 Expression: %s"
      (Expr.to_string (Expr.simplify g.goal_val None))

let format_refuted_goal (rg : refuted_goal) (model : Model.model)
    (var_map : z3_expr Var.Map.t) ~print_path:(print_path : bool) : string =
  let fmt = Format.str_formatter in
  format_goal fmt rg.goal model;
  if print_path then format_path fmt rg.path rg.reg_map var_map;
  Format.flush_str_formatter ()

let goal_of_refuted_goal (rg : refuted_goal) : goal =
  rg.goal

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

let update_current_regs (model : Model.model) (regs : z3_expr list) (vals : z3_expr list)
    (jmp : Jmp.t) (map : reg_map) (filter_out : z3_expr list) : reg_map =
  let registers =
    List.fold (List.zip_exn regs vals) ~init:[]
      ~f:(fun regs (reg, value) ->
          (* Manually removing mem from the list of variables being updated. *)
          if List.exists filter_out ~f:(Expr.equal reg) then
            regs
          else
            (reg, eval_model_exn model value) :: regs)
  in
  (* TODO: Figure out why we shouldn't overwrite the register values if the
     jmp is already in the map. *)
  match Jmp.Map.add map ~key:jmp ~data:registers with
  | `Ok reg_map -> reg_map
  | `Duplicate -> map

let get_refuted_goals ?filter_out:(filter_out = []) (constr : t)
    (solver : Z3.Solver.solver) (ctx : Z3.context) : refuted_goal seq =
  let model = get_model_exn solver in
  let rec worker (constr : t) (current_path : path) (current_registers : reg_map)
      (olds : z3_expr list) (news : z3_expr list) : refuted_goal seq =
    match constr with
    | Goal g ->
      let goal_val = Expr.substitute g.goal_val olds news in
      let goal_res = eval_model_exn model goal_val in
      begin
        match Solver.check solver [goal_res] with
        | Solver.SATISFIABLE -> Seq.empty
        | Solver.UNSATISFIABLE ->
          Seq.singleton
            { goal = { g with goal_val = goal_val};
              path = current_path;
              reg_map = current_registers }
        | Solver.UNKNOWN ->
          failwith (Format.sprintf "get_refuted_goals: Unable to resolve %s" g.goal_name)
      end
    | ITE (jmp, cond, c1, c2) ->
      let cond_val = Expr.substitute cond olds news in
      let cond_res = eval_model_exn model cond_val in
      let current_registers = update_current_regs
          model olds news jmp current_registers filter_out in
      begin
        match Solver.check solver [cond_res] with
        | Solver.SATISFIABLE ->
          let current_path = Jmp.Map.set current_path ~key:jmp ~data:true in
          worker c1 current_path current_registers olds news
        | Solver.UNSATISFIABLE ->
          let current_path = Jmp.Map.set current_path ~key:jmp ~data:false in
          worker c2 current_path current_registers olds news
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
        List.fold concs ~init:Seq.empty ~f:(fun accum c ->
            Seq.append (worker c current_path current_registers olds news) accum)
    | Subst (e, o, n) ->
      let n' = List.map n ~f:(fun x -> Expr.substitute x olds news) in
      worker e current_path current_registers (olds @ o) (news @ n')
  in
  worker constr Jmp.Map.empty Jmp.Map.empty [] []


