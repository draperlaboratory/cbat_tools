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
module Env = Environment
module Constr = Constraint

module VarMap = Var.Map

open Core_kernel
open Bap.Std

let print_result (solver : Z3.Solver.solver) (status : Z3.Solver.status)
    (goals: Constr.t) (ctx : Z3.context) : unit =
  match status with
  | Z3.Solver.UNSATISFIABLE -> Format.printf "\nUNSAT!\n%!"
  | Z3.Solver.UNKNOWN -> Format.printf "\nUNKNOWN!\n%!"
  | Z3.Solver.SATISFIABLE ->
    Format.printf "\nSAT!\n%!";
    let model = Z3.Solver.get_model solver
                |> Option.value_exn ?here:None ?error:None ?message:None in
    Format.printf "\nModel:\n%s\n%!" (Z3.Model.to_string model);
    let refuted_goals = Constr.get_refuted_goals goals solver ctx in
    Format.printf "\nRefuted goals:\n%!";
    Seq.iter refuted_goals ~f:(fun g ->
        Format.printf "%s\n%!" (Constr.refuted_goal_to_string g model))

(** [output_gdb] is similar to [print_result] except chews on the model and outputs a gdb script with a 
    breakpoint at the subroutine and fills the appropriate registers *)

let output_gdb (solver : Z3.Solver.solver) (status : Z3.Solver.status)
    (env : Env.t) ~func:(func : string) ~filename:(gdb_filename : string) : unit =
  match status with
  | Z3.Solver.SATISFIABLE ->
    let model = Z3.Solver.get_model solver
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

