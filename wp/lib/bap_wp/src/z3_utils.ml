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
module Z3Array = Z3.Z3Array
module FuncDecl = Z3.FuncDecl
module Symbol = Z3.Symbol
module Solver = Z3.Solver
module Env = Environment
module Constr = Constraint

let get_decls_and_symbols (env : Env.t) : ((FuncDecl.func_decl * Symbol.symbol) list) =
  let ctx = Env.get_context env in
  let var_to_decl ~key:_ ~data:z3_var decls =
    assert (Expr.is_const z3_var);
    let decl = FuncDecl.mk_const_decl_s ctx
        (Expr.to_string z3_var)
        (Expr.get_sort z3_var) in
    let sym =  Symbol.mk_string ctx (Expr.to_string z3_var) in
    (decl, sym) :: decls
  in
  let var_map = Env.get_var_map env in
  let init_var_map = Env.get_init_var_map env in
  let var_decls = Env.EnvMap.fold var_map ~init:[] ~f:var_to_decl in
  Env.EnvMap.fold init_var_map ~init:var_decls ~f:var_to_decl

let mk_smtlib2 (ctx : Z3.context) (smtlib_str : string)
    (decl_syms : (Z3.FuncDecl.func_decl * Z3.Symbol.symbol) list) : Constr.t =
  let fun_decls, fun_symbols = List.unzip decl_syms in
  let sort_symbols = [] in
  let sorts = [] in
  let asts = Z3.SMT.parse_smtlib2_string ctx smtlib_str
      sort_symbols
      sorts
      fun_symbols
      fun_decls
  in
  let goals = List.map (Z3.AST.ASTVector.to_expr_list asts)
      ~f:(fun e ->
          e
          |> Constr.mk_goal (Expr.to_string e)
          |> Constr.mk_constr)
  in
  Constr.mk_clause [] goals

let tokenize (str : string) : string list =
  let delim = Re.Posix.compile_pat "[ \n\r\t()]" in
  let tokens = Re.split_full delim str in
  List.rev_map tokens ~f:(function
      | `Text t -> t
      | `Delim g ->
        (* There should always be one value in the group. If not, we will raise an
           exception. *)
        assert (Re.Group.nb_groups g = 1);
        Re.Group.get g 0)

let build_str (tokens : string list) : string =
  List.fold tokens ~init:"" ~f:(fun post token -> token ^ post)

(* Looks up a Z3 variable's name in the map based off of the name in BIL notation.
   [fmt] is used to add prefixes and suffixes to a variable name. For example,
   init_RDI_orig. *)
let get_z3_name (map : Constr.z3_expr Var.Map.t) (name : string) (fmt : Var.t -> string)
  : (Z3.Expr.expr option) =
  map
  |> Var.Map.to_alist
  |> List.find_map
    ~f:(fun (var, z3_var) ->
        if String.equal name (fmt var) then
          Some z3_var
        else
          None)

let mk_smtlib2_single (env : Env.t) (smt_post : string) : Constr.t =
  let var_map = Env.get_var_map env in
  let init_var_map = Env.get_init_var_map env in
  let smt_post =
    smt_post
    |> tokenize
    |> List.map ~f:(fun token ->
        match get_z3_name var_map token Var.name with
        | Some n -> n |> Expr.to_string
        | None ->
          begin
            match get_z3_name init_var_map token (fun v -> "init_" ^ Var.name v) with
            | Some n -> n |> Expr.to_string
            | None -> token
          end)
    |> build_str
  in
  info "New smt-lib string : %s\n" smt_post;
  let decl_syms = get_decls_and_symbols env in
  let ctx = Env.get_context env in
  mk_smtlib2 ctx smt_post decl_syms

let construct_pointer_constraint (l: string list) (env1 : Env.t)
    (env2: Env.t option): Constr.t =
  let stack_bottom = Env.get_stack_bottom env1 in
  let ctx = Env.get_context env1 in
  let arch = match Env.get_arch env1 |> Bap.Std.Arch.addr_size with
    | `r32 -> 32
    | `r64 -> 64 in
  let rsp = "RSP" in
  let err_msg_input = "invalid register name in pointer register list" in
  let err_msg_rsp = "stack pointer not found" in
  let sb_bv = Z3.BitVector.mk_numeral ctx (stack_bottom |> Int.to_string) arch in
  let gen_constr = match env2 with
    | Some env2 ->
      let init_var_map_orig = Env.get_init_var_map env1 in
      let init_var_map_mod = Env.get_init_var_map env2 in
      let rsp_orig = Option.value_exn ~message:("original " ^ err_msg_rsp)
          (get_z3_name init_var_map_orig rsp Var.name) in
      let rsp_mod = Option.value_exn ~message:("modified " ^ err_msg_rsp)
          (get_z3_name init_var_map_mod rsp Var.name) in
      (* Encode constraint for each register and wrap them up in a massive and *)
      (fun acc reg ->
         (* we do want exceptions here if the register names are invalid
          *  or RSP doesn't exist *)
         let reg_name_orig = Option.value_exn ~message:err_msg_input
             (get_z3_name init_var_map_orig reg Var.name) in
         let reg_name_mod = Option.value_exn ~message:err_msg_input
             (get_z3_name init_var_map_mod reg Var.name) in
         (* the pointer register must be above RSP
          *  NOTE: we are assuming stack grows down *)
         let uge_1 = Z3.BitVector.mk_uge ctx reg_name_orig rsp_orig in
         let uge_2 = Z3.BitVector.mk_uge ctx reg_name_mod rsp_mod in
         (* the pointer must be below the bottom of the stack *)
         let ule_1 =  Z3.BitVector.mk_ule ctx reg_name_orig sb_bv in
         let ule_2 =  Z3.BitVector.mk_ule ctx reg_name_mod sb_bv in
         (* encode that the pointer is outside the uninitialized stack region *)
         let or_c_1 = Z3.Boolean.mk_or ctx [uge_1; ule_1] in
         let or_c_2 = Z3.Boolean.mk_or ctx [uge_2; ule_2] in
         let and_c = Z3.Boolean.mk_and ctx [or_c_1; or_c_2;] in
         Z3.Boolean.mk_and ctx [and_c; acc]
      )
    | None ->
      let init_var_map = Env.get_init_var_map env1 in
      let stack_pointer = Option.value_exn ~message:err_msg_rsp
          (get_z3_name init_var_map rsp Var.name) in
      (fun acc reg ->
         let reg_name = Option.value_exn ~message:err_msg_input
             (get_z3_name init_var_map reg Var.name)in
         let uge = Z3.BitVector.mk_ugt ctx reg_name stack_pointer in
         let ule = Z3.BitVector.mk_ult ctx reg_name sb_bv in
         let or_c = Z3.Boolean.mk_or ctx [uge; ule] in
         Z3.Boolean.mk_and ctx [or_c; acc]
      )
  in
  let expr = List.fold l ~init:(Z3.Boolean.mk_true ctx) ~f:gen_constr in
  Constr.mk_goal "pointer_precond" expr |> Constr.mk_constr
