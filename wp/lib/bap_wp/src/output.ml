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
module Solver = Z3.Solver
module Model = Z3.Model
module Fun = Z3.FuncDecl
module FInterp = Model.FuncInterp
module Env = Environment
module Constr = Constraint

module VarMap = Var.Map

let format_values (fmt : Format.formatter) (vals : (Var.t * Constr.z3_expr) list) : unit =
  List.iter vals
    ~f:(fun (var, value) ->
        let var_str = Var.to_string var in
        let pad_size = Int.max (5 - (String.length var_str)) 1 in
        let pad = String.make pad_size ' ' in
        Format.fprintf fmt
          "\t%s%s|->  @[%s@]@\n" var_str pad (Expr.to_string value))

let format_model (model : Model.model) (env1 : Env.t) (_env2 : Env.t) : string =
  let var_map = Env.get_var_map env1 in
  let key_val = Env.EnvMap.fold var_map ~init:[]
      ~f:(fun ~key ~data pairs ->
          let value = Constr.eval_model_exn model data in
          (key, value)::pairs)
  in
  let fmt = Format.str_formatter in
  format_values fmt key_val;
  let fun_defs =
    model
    |> Model.get_func_decls
    |> List.map ~f:(fun def ->
        let interp = Option.value_exn (Model.get_func_interp model def) in
        (def, interp))
  in
  Format.fprintf fmt "\n";
  List.iter fun_defs ~f:(fun (def, interp) ->
      Format.fprintf fmt "%s  %s\n" (Fun.to_string def) (FInterp.to_string interp));
  Format.flush_str_formatter ()

let format_registers (fmt : Format.formatter) (regs : Constr.reg_map) (jmp : Jmp.t)
    (env : Env.t) : unit =
  match Jmp.Map.find regs jmp with
  | None -> ()
  | Some regs ->
    let var_map = Env.get_var_map env in
    let reg_vals = VarMap.fold var_map ~init:[]
        ~f:(fun ~key ~data pairs ->
            let regs = List.find_map regs ~f:(fun (r, value) ->
                if Expr.equal data r then Some (key, value) else None) in
            match regs with
            | None -> pairs
            | Some r -> r :: pairs)
    in
    format_values fmt reg_vals;
    Format.fprintf fmt "\n%!"

let format_path (fmt : Format.formatter) (p : Constr.path) (regs : Constr.reg_map)
    (env : Env.t) : unit =
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
          | None -> Format.fprintf fmt "\t%s %s (Address not found) \n%!" jmp_str taken_str
          | Some addr ->
            Format.fprintf fmt "\t%s %s (Address: %s)\n%!"
              jmp_str taken_str (Addr.to_string addr)
        end;
        format_registers fmt regs jmp env)

let format_goal (fmt : Format.formatter) (g : Constr.goal) (model : Model.model) : unit =
  let goal_name = Constr.get_goal_name g in
  let goal_val = Constr.get_goal_val g in
  Format.fprintf fmt "%s:" goal_name;
  if Bool.is_eq goal_val then
    begin
      let args = Expr.get_args goal_val in
      Format.fprintf fmt "\n\tConcrete values: = ";
      List.iter args ~f:(fun arg ->
          let value = Constr.eval_model_exn model arg in
          Format.fprintf fmt "%s " (Expr.to_string value));
      Format.fprintf fmt "\n\tZ3 Expression: = ";
      List.iter args ~f:(fun arg ->
          let simplified = Expr.simplify arg None in
          Format.fprintf fmt "%s " (Expr.to_string simplified));
    end
  else
    Format.fprintf fmt "\n\tZ3 Expression: %s"
      (Expr.to_string (Expr.simplify goal_val None))

(* Creates a string representation of a goal that has been refuted given the model.
   This string shows the lhs and rhs of a goal that compares two values. *)
let format_refuted_goal (rg : Constr.refuted_goal) (model : Model.model) (env : Env.t)
  : string =
  let fmt = Format.str_formatter in
  format_goal fmt rg.goal model;
  format_path fmt rg.path rg.reg_map env;
  Format.flush_str_formatter ()

type mem_model = {default : Constr.z3_expr ; model : (Constr.z3_expr * Constr.z3_expr) list}

(** [extract_array] takes a z3 expression that is a seqeunce of store and converts it into
    a mem_model, which consists of a key/value association list and a default value *)

let extract_array (e : Constr.z3_expr) : mem_model  = 
      let rec extract_array' (partial_map : (Constr.z3_expr * Constr.z3_expr) list) (e : Constr.z3_expr) : mem_model =
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
                warning "Unexpected case destructing Z3 array: %s" (Z3.Expr.to_string e);
                {default = e ; model = partial_map}
                end
      in
      extract_array' [] e

let is_x86 (a : Arch.t) : bool =
  match a with
  | #Arch.x86 -> true
  | _ -> false

let get_mem (m : Z3.Model.model) (env : Env.t) : mem_model option =
    let arch = Env.get_arch env in
    if is_x86 arch then
    begin
      let module Target = (val target_of_arch arch) in
      let mem, _ = Env.get_var env Target.CPU.mem in
      Some (extract_array (Constr.eval_model_exn m mem))
    end
    else
      None



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
    let refuted_goals = Constr.get_refuted_goals goals solver ctx in
    Format.printf "\nRefuted goals:\n%!";
    Seq.iter refuted_goals ~f:(fun goal ->
        Format.printf "%s\n%!" (format_refuted_goal goal model env1))

(** [output_gdb] is similar to [print_result] except chews on the model and outputs a gdb script with a
    breakpoint at the subroutine and fills the appropriate registers *)

let expr_to_hex (e : Constr.z3_expr) : string = Z3.Expr.to_string e |> String.substr_replace_first ~pattern:"#" ~with_:"0"

let output_gdb (solver : Solver.solver) (status : Solver.status)
    (env : Env.t) ~func:(func : string) ~filename:(gdb_filename : string) : unit =
  match status with
  | Solver.SATISFIABLE ->
    let model = Constr.get_model_exn solver in
    let option_mem_model = get_mem model env in
    let varmap = Env.get_var_map env in
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
