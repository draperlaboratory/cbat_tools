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
module Arith = Z3.Arithmetic
module BV = Z3.BitVector
module Bool = Z3.Boolean
module Array = Z3.Z3Array
module Solver = Z3.Solver
module Model = Z3.Model
module Fun = Z3.FuncDecl
module FInterp = Model.FuncInterp
module Env = Environment
module Constr = Constraint

module VarMap = Var.Map

open Core_kernel
open Bap.Std


let format_model (model : Model.model) (env1 : Env.t) (_env2 : Env.t) : string =
  let var_map = Env.get_var_map env1 in
  let key_val = Env.EnvMap.fold var_map ~init:[]
      ~f:(fun ~key ~data pairs ->
          let value = Option.value_exn (Model.eval model data true) in
          (key, value)::pairs)
  in
  let fmt = Format.str_formatter in
  List.iter key_val
    ~f:(fun (var, value) ->
        let var_str = Var.to_string var in
        let pad_size = Int.max (5 - (String.length var_str)) 1 in 
        let pad = String.make pad_size ' ' in
        Format.fprintf fmt
          "%s%s|->  @[%s@]@\n" var_str pad (Expr.to_string value));
  let fun_defs = model |> Model.get_func_decls
                 |> List.map ~f:(fun def ->
                     let interp = Option.value_exn (Model.get_func_interp model def) in
                     (def, interp))
  in
  Format.fprintf fmt "\n";
  List.iter fun_defs ~f:(fun (def, interp) ->
      Format.fprintf fmt "%s  %s\n" (Fun.to_string def) (FInterp.to_string interp));
  Format.flush_str_formatter ()


let print_result (solver : Solver.solver) (status : Solver.status)
    (goals: Constr.t) ~orig:(env1 : Env.t) ~modif:(env2 : Env.t) : unit =
  let ctx = Env.get_context env1 in
  match status with
  | Solver.UNSATISFIABLE -> Format.printf "\nUNSAT!\n%!"
  | Solver.UNKNOWN -> Format.printf "\nUNKNOWN!\n%!"
  | Solver.SATISFIABLE ->
    Format.printf "\nSAT!\n%!";
    let model = Solver.get_model solver
                |> Option.value_exn ?here:None ?error:None ?message:None in
    Format.printf "\nModel:\n%s\n%!" (format_model model env1 env2);
    let refuted_goals = Constr.get_refuted_goals goals solver ctx in
    Format.printf "\nRefuted goals:\n%!";
    Seq.iter refuted_goals ~f:(fun g ->
        Format.printf "%s\n%!" (Constr.refuted_goal_to_string g model))

(** [output_gdb] is similar to [print_result] except chews on the model and outputs a gdb script with a 
    breakpoint at the subroutine and fills the appropriate registers *)

let output_gdb (solver : Solver.solver) (status : Solver.status)
    (env : Env.t) ~func:(func : string) ~filename:(gdb_filename : string) : unit =
  match status with
  | Solver.SATISFIABLE ->
    let model = Solver.get_model solver
                |> Option.value_exn ?here:None ?error:None ?message:None in
    let varmap = Env.get_var_map env in 
    let module Target = (val target_of_arch (Env.get_arch env)) in
    let regmap = VarMap.filter_keys ~f:(Target.CPU.is_reg) varmap in
    let reg_val_map = VarMap.map ~f:(fun z3_reg -> Option.value_exn (Z3.Model.eval model z3_reg true)) regmap in
    Out_channel.with_file gdb_filename  ~f:(fun t -> 
        Printf.fprintf t "break *%s\n" func; (* The "*" is necessary to break before some slight setup *)
        Printf.fprintf t "start\n";
        VarMap.iteri reg_val_map ~f:(fun ~key ~data -> 
            let hex_value = Z3.Expr.to_string data |> String.substr_replace_first ~pattern:"#" ~with_:"0" in
            Printf.fprintf t "set $%s = %s \n" (String.lowercase (Var.name key)) hex_value;
        ))
  | _ -> ()

