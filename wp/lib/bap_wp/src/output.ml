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

type mem_model = {default : Constr.z3_expr ; model : (Constr.z3_expr * Constr.z3_expr) list}

let format_mem_model (fmt : Format.formatter) (mem_model : mem_model) : unit =
  mem_model.model
  |> List.sort ~compare:(fun (addr1, _) (addr2, _) ->
      String.compare (Expr.to_string addr1) (Expr.to_string addr2))
  |> List.iter ~f:(fun (key, data) ->
      Format.fprintf fmt "\t\t%s |-> %s ;\n"
        (Expr.to_string key) (Constr.expr_to_hex data));
  Format.fprintf fmt "\t\telse |-> %s]\n" (Constr.expr_to_hex mem_model.default)

(** [extract_array] takes a z3 expression that is a seqeunce of store and converts it into
    a mem_model, which consists of a key/value association list and a default value *)

let extract_array (e : Constr.z3_expr) : mem_model =
  let rec extract_array' (partial_map : (Constr.z3_expr * Constr.z3_expr) list) (e : Constr.z3_expr) : mem_model =
    let numargs = Z3.Expr.get_num_args e in
    let args = Z3.Expr.get_args e in
    let f_decl = Z3.Expr.get_func_decl e in
    let f_name = Z3.FuncDecl.get_name f_decl |> Z3.Symbol.to_string in
    if Int.(numargs = 3) && String.(f_name = "store") then begin
      let next_arr = List.nth_exn args 0 in
      let key = List.nth_exn args 1 in
      let value = List.nth_exn args 2 in
      extract_array' ((key , value) :: partial_map) next_arr
    end
    else if Int.(numargs = 1) && String.(f_name = "const") then begin
      let key = List.nth_exn args 0 in
      { default = key; model = List.rev partial_map }
    end
    else begin
      warning "Unexpected case destructing Z3 array: %s" (Z3.Expr.to_string e);
      { default = e ; model = partial_map }
    end
  in
  extract_array' [] e

let print_registers (fmt : Format.formatter) (model : Model.model)
    (reg_map : Constr.z3_expr Var.Map.t) : unit =
  let key_val = Env.EnvMap.fold reg_map ~init:[]
      ~f:(fun ~key ~data pairs ->
          if Var.is_physical key then
            let key_str = Var.to_string key in
            let value = Constr.eval_model_exn model data in
            (key_str, value) :: pairs
          else
            pairs)
  in
  Constr.format_values fmt key_val

(* We should pass in env2 because the values of memory can differ in the second
   environment. We need to get the Z3 name for the memory in env2 because the
   memory map pnly contains the Z3 name for the memory in env1. *)
let print_memory (fmt : Format.formatter) (model : Model.model)
    (mem_map : Constr.z3_expr Var.Map.t) (env2 : Env.t) : unit =
  Env.EnvMap.iteri mem_map ~f:(fun ~key ~data:mem_orig ->
      let key_str = Var.to_string key in
      let mem_mod, _ = Env.get_var env2 key in
      let val_orig = Constr.eval_model_exn model mem_orig in
      let val_mod = Constr.eval_model_exn model mem_mod in
      Format.fprintf fmt "\t%s_orig |-> [\n" key_str;
      format_mem_model fmt (extract_array val_orig);
      (* Memory does not have to be equivalent between both binaries, and in the
         case where they differ, show both orig and mod memories. *)
      if not (Expr.equal val_orig val_mod) then
        begin
          Format.fprintf fmt "\t%s_mod |-> [\n" key_str;
          format_mem_model fmt (extract_array val_mod)
        end
      else Format.fprintf fmt "\t%s_mod = %s_orig" key_str key_str
    )

(* These are the constants that were generated during the analysis. *)
let print_constants (fmt : Format.formatter) (model : Model.model)
    (consts : Env.ExprSet.t) : unit =
  let const_vals =
    Env.ExprSet.fold consts ~init:[] ~f:(fun pairs c ->
        let name = Expr.to_string c in
        let value = Constr.eval_model_exn model c in
        (name, value) :: pairs)
  in
  Format.fprintf fmt "\n%!";
  Constr.format_values fmt const_vals

let print_fun_decls (fmt : Format.formatter) (model : Model.model) : unit =
  let fun_defs =
    model
    |> Model.get_func_decls
    |> List.map ~f:(fun def ->
        let interp = Option.value_exn (Model.get_func_interp model def) in
        (def, interp))
  in
  Format.fprintf fmt "\n";
  List.iter fun_defs ~f:(fun (def, interp) ->
      Format.fprintf fmt "%s  %s\n" (Fun.to_string def) (FInterp.to_string interp))

let format_model (model : Model.model) (env1 : Env.t) (env2 : Env.t) : string =
  let fmt = Format.str_formatter in
  let arch = Env.get_arch env1 in
  let module Target = (val target_of_arch arch) in
  let var_map = Env.get_var_map env1 in
  let mem_map, reg_map =
    Env.EnvMap.partitioni_tf var_map ~f:(fun ~key ~data:_ -> Target.CPU.is_mem key)
  in
  let consts = Env.ExprSet.union (Env.get_consts env1) (Env.get_consts env2) in
  print_registers fmt model reg_map;
  print_memory fmt model mem_map env2;
  print_constants fmt model consts;
  print_fun_decls fmt model;
  Format.flush_str_formatter ()

let get_mem (m : Z3.Model.model) (env : Env.t) : mem_model option =
  let arch = Env.get_arch env in
  if Env.is_x86 arch then
    begin
      let module Target = (val target_of_arch arch) in
      let mem, _ = Env.get_var env Target.CPU.mem in
      Some (extract_array (Constr.eval_model_exn m mem))
    end
  else
    None

let print_result (solver : Solver.solver) (status : Solver.status) (goals: Constr.t)
    ~show:(show : string list) ~orig:(env1, sub1 : Env.t * Sub.t)
    ~modif:(env2, sub2 : Env.t * Sub.t) ~formatter:(formatter: string option) : unit =
  let formatter = match formatter with
    | Some "stdout" -> Format.fprintf Format.std_formatter 
    | _ -> Format.fprintf Format.err_formatter in 
    match status with
  | Solver.UNSATISFIABLE -> formatter "%s%!" "\nUNSAT!\n%!"
  | Solver.UNKNOWN -> formatter "%s%!" "\nUNKNOWN!\n%!"
  | Solver.SATISFIABLE ->
    let module Target = (val target_of_arch (Env.get_arch env1)) in
    let ctx = Env.get_context env1 in
    let model = Constr.get_model_exn solver in
    formatter "%s%!" "\nSAT!\n%!";
    formatter "\nModel:\n%s\n%!" (format_model model env1 env2);
    let print_refuted_goals = List.mem show "refuted-goals" ~equal:String.equal in
    let print_path = List.mem show "paths" ~equal:String.equal in
    (* If 'paths' is specified, we assume we are also printing the refuted goals. *)
    if print_refuted_goals || print_path then begin
      let var_map1 = Env.get_var_map env1 in
      let var_map2 = Env.get_var_map env2 in
      let mem1, _ = Env.get_var env1 Target.CPU.mem in
      let mem2, _ = Env.get_var env2 Target.CPU.mem in
      let refuted_goals =
        Constr.get_refuted_goals goals solver ctx ~filter_out:[mem1; mem2] in
      formatter "%s%!" "\nRefuted goals:\n%!";
      Seq.iter refuted_goals ~f:(fun goal ->
          formatter "%s\n%!"
            (Constr.format_refuted_goal goal model ~orig:(var_map1, sub1)
               ~modif:(var_map2, sub2) ~print_path))
    end

(** [output_gdb] is similar to [print_result] except chews on the model and outputs a gdb script with a
    breakpoint at the subroutine and fills the appropriate registers *)
let output_gdb (solver : Solver.solver) (status : Solver.status)
    (env : Env.t) ~func:(func : string) ~filename:(gdb_filename : string) : unit =
  match status with
  | Solver.SATISFIABLE ->
    info "Dumping gdb script to file: %s\n" gdb_filename;
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
            let hex_value = Constr.expr_to_hex data in
            Printf.fprintf t "set $%s = %s \n" (String.lowercase (Var.name key)) hex_value;
          );
        match option_mem_model with
        | None -> ()
        | Some mem_model ->  List.iter mem_model.model ~f:(fun (addr,value) ->
            Printf.fprintf t "set {int}%s = %s \n"
              (Constr.expr_to_hex addr) (Constr.expr_to_hex value))
      )
  | _ -> info "Result of analysis is not SAT. No GDB script to output.\n%!"

let output_bildb (solver : Solver.solver) (status : Solver.status) (env : Env.t)
    (filename : string) : unit =
  match status with
  | Solver.SATISFIABLE ->
    info "Outputting BilDB init script to %s\n%!" filename;
    let module Target = (val target_of_arch (Env.get_arch env)) in
    let model = Constr.get_model_exn solver in
    let mem_model = get_mem model env in
    let var_map = Env.get_var_map env in
    let reg_map = VarMap.filter_keys ~f:(Target.CPU.is_reg) var_map in
    let reg_vals =  VarMap.map reg_map ~f:(fun z3_reg ->
        Constr.eval_model_exn model z3_reg)
    in
    Out_channel.with_file filename ~f:(fun t ->
        (* Print registers and their values to file if present in the model. *)
        if not @@ VarMap.is_empty reg_vals then begin
          Printf.fprintf t "Variables:\n";
          VarMap.iteri reg_vals ~f:(fun ~key ~data ->
              let hex_value = Constr.expr_to_hex data in
              Printf.fprintf t "  %s: %s\n" (Var.name key) hex_value)
        end;
        (* Print memory addresses and the values they hold if present in the model. *)
        match mem_model with
        | None -> ()
        | Some m ->
          if not @@ List.is_empty m.model then begin
            Printf.fprintf t "Locations:\n";
            List.iter m.model ~f:(fun (addr, value) ->
                Printf.fprintf t "  %s: %s\n"
                  (Constr.expr_to_hex addr) (Constr.expr_to_hex value))
          end
      )
  | _ -> info "Result of analysis is not SAT. No BilDB init script to output.\n%!"
