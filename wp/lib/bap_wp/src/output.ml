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

open !Core
open Bap.Std
open Bap_core_theory

include Self()

module Expr = Z3.Expr
module Bool = Z3.Boolean
module Solver = Z3.Solver
module Model = Z3.Model
module Fun = Z3.FuncDecl
module Z3Array = Z3.Z3Array
module FInterp = Model.FuncInterp
module Env = Environment
module Constr = Constraint
module Comp = Compare
module Sym = Z3.Symbol
module VarMap = Var.Map

type mem_model = {
  default : Constr.z3_expr;
  model : (Constr.z3_expr * Constr.z3_expr) list
}

let equal_mem_model (m1 : mem_model) (m2 : mem_model) : bool =
  let eqe (k1, v1) (k2, v2) = Expr.equal k1 k2 && Expr.equal v1 v2 in
  Expr.equal m1.default m2.default &&
  List.equal eqe m1.model m2.model

let format_mem_model (fmt : Format.formatter) (mem_model : mem_model) : unit =
  mem_model.model |> List.iter ~f:(fun (key, data) ->
      Format.fprintf fmt "\t\t%s |-> %s ;\n"
        (Expr.to_string key) (Constr.expr_to_hex data));
  if (Expr.is_numeral mem_model.default)
  then Format.fprintf fmt "\t\telse |-> %s]\n" (Constr.expr_to_hex mem_model.default)
  else Format.fprintf fmt "\t\t%s]\n" (Expr.to_string mem_model.default)

(* Takes a z3 expression that is either a sequence of stores or a lambda term
   and converts it into a mem_model, which consists of a key/value association
   list and a default value *)
let extract_array (e : Constr.z3_expr) : mem_model =
  let rec aux
      (partial_map : (Constr.z3_expr * Constr.z3_expr) list)
      (e : Constr.z3_expr) : mem_model =
    let bail () =
      warning "Unexpected case destructing Z3 array: %s" @@ Expr.to_string e;
      {default = e; model = partial_map} in
    if Z3Array.is_array e then
      let numargs = Expr.get_num_args e in
      let args = Expr.get_args e in
      let f_decl = Expr.get_func_decl e in
      let f_name = Fun.get_name f_decl |> Sym.to_string in
      match f_name with
      | "store" when numargs = 3 ->
        let next_arr = List.nth_exn args 0 in
        let key = List.nth_exn args 1 in
        let value = List.nth_exn args 2 in
        aux ((key, value) :: partial_map) next_arr
      | "const" when numargs = 1 ->
        let key = List.nth_exn args 0 in
        {default = key; model = List.rev partial_map}
      | _ -> bail ()
    else bail () in
  let mem = aux [] e in {
    mem with model = List.sort mem.model ~compare:(fun (addr1, _) (addr2, _) ->
      String.compare (Expr.to_string addr1) (Expr.to_string addr2))
  }

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
      let ex_orig = extract_array val_orig in
      let ex_mod = extract_array val_mod in
      Format.fprintf fmt "\t%s_orig |-> [\n" key_str;
      format_mem_model fmt ex_orig;
      (* Memory does not have to be equivalent between both binaries, and in the
         case where they differ, show both orig and mod memories. *)
      if not @@ equal_mem_model ex_orig ex_mod then begin
        Format.fprintf fmt "\t%s_mod |-> [\n" key_str;
        format_mem_model fmt ex_mod
      end else Format.fprintf fmt "\t%s_mod = %s_orig" key_str key_str)

(* These are the constants and function call predicates that were generated
   during the analysis. *)
let print_call_preds (fmt : Format.formatter) (model : Model.model)
    (preds : Env.ExprSet.t) : unit =
  Format.fprintf fmt "\n%!";
  let arrays, consts =
    Env.ExprSet.partition_tf preds ~f:Z3Array.is_array
  in
  Env.ExprSet.iter arrays ~f:(fun a ->
      Format.fprintf fmt "\t%s |-> [\n" (Expr.to_string a);
      let value = Constr.eval_model_exn model a in
      format_mem_model fmt (extract_array value));
  let pred_vals =
    Env.ExprSet.fold consts ~init:[] ~f:(fun pairs c ->
        let name = Expr.to_string c in
        let value = Constr.eval_model_exn model c in
        (name, value) :: pairs)
  in
  Constr.format_values fmt pred_vals

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
      Format.fprintf fmt "%s  %s\n"
        (Fun.to_string def)
        (FInterp.to_string interp))

let format_model (model : Model.model) (env1 : Env.t) (env2 : Env.t) : string =
  let fmt = Format.str_formatter in
  let var_map = Env.get_var_map env1 in
  let mem_map, reg_map =
    Env.EnvMap.partitioni_tf var_map
      ~f:(fun ~key ~data:_ ->
          Var.((Env.get_mem env1) = key))
  in
  let call_preds = Env.ExprSet.union
      (Env.get_call_preds env1) (Env.get_call_preds env2) in
  print_registers fmt model reg_map;
  print_memory fmt model mem_map env2;
  print_call_preds fmt model call_preds;
  print_fun_decls fmt model;
  Format.flush_str_formatter ()

let get_mem (m : Z3.Model.model) (env : Env.t) : mem_model =
  let mem, _ = Env.get_var env (Env.get_mem env) in
  extract_array (Constr.eval_model_exn m mem)

let print_result ?fmt:(fmt = Format.err_formatter) (solver : Solver.solver)
      (status : Solver.status) (goals: Constr.t) ~show:(show : string list)
      ~orig:(Comp.{env=env1; prog=sub1; _}) ~modif:(Comp.{env=env2; prog=sub2; _}) : unit =
  match status with
  | Solver.UNSATISFIABLE -> Format.fprintf fmt "%s%!" "\nNo counterexample found.\n"
  | Solver.UNKNOWN -> Format.fprintf fmt "%s%!" "\nZ3 timed out.\n"
  | Solver.SATISFIABLE ->
    let ctx = Env.get_context env1 in
    let model = Constr.get_model_exn solver in
    Format.fprintf fmt "%s%!" "\nProperty falsified. Counterexample found.\n";
    Format.fprintf fmt "\nModel:\n%s\n%!" (format_model model env1 env2);
    let print_refuted_goals = List.mem show "refuted-goals" ~equal:String.equal in
    let print_path = List.mem show "paths" ~equal:String.equal in
    (* If 'paths' is specified, we assume we are also printing the refuted goals. *)
    if print_refuted_goals || print_path then
      let var_map1 = Env.get_var_map env1 in
      let var_map2 = Env.get_var_map env2 in
      let mem1, _ = Env.get_var env1 (Env.get_mem env1) in
      let mem2, _ = Env.get_var env2 (Env.get_mem env2) in
      let refuted_goals =
        Constr.get_refuted_goals goals solver ctx ~filter_out:[mem1; mem2] in
      begin
        Format.fprintf fmt "%s%!" "\nRefuted goals:\n";
        Seq.iter refuted_goals ~f:(fun goal ->
            Format.fprintf fmt "%s\n%!"
              (Constr.format_refuted_goal goal model ~orig:(var_map1, sub1)
                 ~modif:(var_map2, sub2) ~print_path));
        if print_path then
          Cfg_path.pp_cfg_path_fst_refuted_goal refuted_goals ~f:sub1 ~g:sub2
            ~f_out:(Sub.name sub1 ^ "_orig.dot") ~g_out:(Sub.name sub2 ^ "_mod.dot")
      end


let reg_map (env : Env.t) =
  let varmap = Env.get_var_map env in
  let target = (Env.get_target env) in
  (* to_core casts a Bap.Std.Var.t to a Theory.Var.t *)
  let to_core v = Theory.Var.create (Var.sort v) (Var.ident v) in
  (* Returns true iff the variable is a GPR for [target] *)
  let is_reg v = Theory.Target.has_roles target [Theory.Role.Register.general] (to_core v) in
  VarMap.filter_keys ~f:is_reg varmap


(** [output_gdb] is similar to [print_result] except chews on the model and outputs a gdb script with a
    breakpoint at the subroutine and fills the appropriate registers *)
let output_gdb (solver : Solver.solver) (status : Solver.status)
    (env : Env.t) ~func:(func : string) ~filename:(gdb_filename : string) : unit =
  match status with
  | Solver.SATISFIABLE ->
    info "Dumping gdb script to file: %s\n" gdb_filename;
    let model = Constr.get_model_exn solver in
    let mem_model = get_mem model env in
    let reg_map = reg_map env in
    let reg_val_map = VarMap.map ~f:(fun z3_reg -> Constr.eval_model_exn model z3_reg) reg_map in
    Out_channel.with_file gdb_filename  ~f:(fun t ->
        (* The "*" is necessary to break before some slight setup *)
        Printf.fprintf t "break *%s\n" func;
        Printf.fprintf t "run\n";
        VarMap.iteri reg_val_map ~f:(fun ~key ~data ->
            let hex_value = Constr.expr_to_hex data in
            Printf.fprintf t "set $%s = %s \n" (String.lowercase (Var.name key)) hex_value;
          );
        List.iter mem_model.model ~f:(fun (addr,value) ->
            Printf.fprintf t "set {int}%s = %s \n"
              (Constr.expr_to_hex addr) (Constr.expr_to_hex value))
      )
  | _ -> info "Result of analysis is not SAT. No GDB script to output.\n%!"

let output_bildb (solver : Solver.solver) (status : Solver.status) (env : Env.t)
    (filename : string) : unit =
  match status with
  | Solver.SATISFIABLE ->
    info "Outputting BilDB init script to %s\n%!" filename;
    let model = Constr.get_model_exn solver in
    let mem_model = get_mem model env in
    let reg_map = reg_map env in
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
        if not @@ List.is_empty mem_model.model then begin
          Printf.fprintf t "Locations:\n";
          List.iter mem_model.model ~f:(fun (addr, value) ->
              Printf.fprintf t "  %s: %s\n"
                (Constr.expr_to_hex addr) (Constr.expr_to_hex value))
        end
      )
  | _ -> info "Result of analysis is not SAT. No BilDB init script to output.\n%!"
