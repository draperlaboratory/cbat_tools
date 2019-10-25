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
          let value = Constr.eval_model_exn model data in
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


type mem_model = {default : Z3.Expr.expr ; model : (Z3.Expr.expr * Z3.Expr.expr) list}

(** [extract_array] takes a z3 expression that is a seqeunce of store and converts it into
    a mem_model, which consists of a key/value association list and a default value *)

let extract_array (e : Z3.Expr.expr) : mem_model  = 
      let rec extract_array' (partial_map : (Z3.Expr.expr * Z3.Expr.expr) list) (e : Z3.Expr.expr) : mem_model =
          Printf.printf "%s\n" (Z3.Expr.to_string e);
          let numargs = Z3.Expr.get_num_args e in
          let args = Z3.Expr.get_args e in
          let f_decl = Z3.Expr.get_func_decl e in
          let f_name = Z3.FuncDecl.get_name f_decl |> Z3.Symbol.to_string in
          if ( Int.(numargs = 3) && String.(f_name = "store"))
          then begin 
                let next_arr = List.nth_exn args 0 in
                let key = List.nth_exn args 1 in
                let value = List.nth_exn args 2 in
                extract_array' (( key , value ) :: partial_map) next_arr
                end
          else if ( Int.(numargs = 1) && String.(f_name = "const")) then begin
                let key = List.nth_exn args 0 in
                { default = key; model = List.rev partial_map}
                end
          else begin
                Printf.printf "Unpexpected case destructing Z3 array: %s" f_name;
                {default = e ; model = partial_map}
                end
      in
      extract_array' [] e


module F = Z3.Model.FuncInterp

let get_mem (m : Z3.Model.model) : mem_model option =
   let decls = Z3.Model.get_decls m |> List.filter ~f:(fun decl -> (Z3.Symbol.to_string (Z3.FuncDecl.get_name decl)) = "mem0") in
   match (List.hd decls) with
   | None -> Printf.printf "No mem0 found.";
             None
   | Some f_decl -> let f_interp = Option.value_exn (Z3.Model.get_const_interp m f_decl) in
                    Some (extract_array f_interp)


let print_result (solver : Solver.solver) (status : Solver.status)
    (goals: Constr.t) ~orig:(env1 : Env.t) ~modif:(env2 : Env.t) : unit =
  let ctx = Env.get_context env1 in
  match status with
  | Solver.UNSATISFIABLE -> Format.printf "\nUNSAT!\n%!"
  | Solver.UNKNOWN -> Format.printf "\nUNKNOWN!\n%!"
  | Solver.SATISFIABLE ->
    Format.printf "\nSAT!\n%!";
    let model = Constr.get_model_exn solver in
    Format.printf "\nModel:\n%s\n%!" (format_model model env1 env2);
    let refuted_goals = Constr.get_refuted_goals_and_paths goals solver ctx in
    Format.printf "\nRefuted goals:\n%!";
    Seq.iter refuted_goals ~f:(fun (goal, path) ->
        Format.printf "%s\n%!" (Constr.refuted_goal_to_string goal model);
        Format.printf "\t%s%!" (Constr.path_to_string path))

(** [output_gdb] is similar to [print_result] except chews on the model and outputs a gdb script with a
    breakpoint at the subroutine and fills the appropriate registers *)

let expr_to_hex (e : Z3.Expr.expr) : string = Z3.Expr.to_string e |> String.substr_replace_first ~pattern:"#" ~with_:"0"

let output_gdb (solver : Solver.solver) (status : Solver.status)
    (env : Env.t) ~func:(func : string) ~filename:(gdb_filename : string) : unit =
  match status with
  | Solver.SATISFIABLE ->
<<<<<<< HEAD
    let model = Constr.get_model_exn solver in
    let varmap = Env.get_var_map env in
=======
    Printf.printf "Z3 Version: %s\n" (Z3.Version.to_string);
    let model = Solver.get_model solver
                |> Option.value_exn ?here:None ?error:None ?message:None in
    let option_mem_model = get_mem model in
    let varmap = Env.get_var_map env in 
>>>>>>> 874382e... Tests and simple mem-model extractor for gdb
    let module Target = (val target_of_arch (Env.get_arch env)) in
    let regmap = VarMap.filter_keys ~f:(Target.CPU.is_reg) varmap in 
    let reg_val_map = VarMap.map ~f:(fun z3_reg -> Constr.eval_model_exn model z3_reg) regmap in
    Out_channel.with_file gdb_filename  ~f:(fun t ->
        Printf.fprintf t "break *%s\n" func; (* The "*" is necessary to break before some slight setup *)
        Printf.fprintf t "run\n";
        VarMap.iteri reg_val_map ~f:(fun ~key ~data -> 
            let hex_value = expr_to_hex data in
            Printf.fprintf t "set $%s = %s \n" (String.lowercase (Var.name key)) hex_value;
        );
        match option_mem_model with
        | None -> ()
        | Some mem_model ->  List.iter mem_model.model ~f:(fun (addr,value) -> 
                             Printf.fprintf t "set {int}%s = %s \n" (expr_to_hex addr) (expr_to_hex value)  );
                             ()
    )
  | _ -> ()
