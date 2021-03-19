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

(** [mk_smtlib2] parses a smtlib2 string in the context that has a mapping of func_decl
    to symbols and returns a constraint [Constr.t] corresponding to the smtlib2 string.
    The [func_decl * symbol] mapping can be constructed from an [Env.t] using the
    [get_decls_and_symbols] function. *)
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
  : (Constr.z3_expr option) =
  map
  |> Var.Map.to_alist
  |> List.find_map
    ~f:(fun (var, z3_var) ->
        if String.equal name (fmt var) then
          Some z3_var
        else
          None)

(** [mk_smtlib2_compare] builds a constraint out of an smtlib2 string that can be used
    as a comparison predicate between an original and modified binary. *)
let mk_smtlib2_compare (env1 : Env.t) (env2 : Env.t) (smtlib_str : string) : Constr.t =
  let var_map1 = Env.get_var_map env1 in
  let var_map2 = Env.get_var_map env2 in
  let init_var_map1 = Env.get_init_var_map env1 in
  let init_var_map2 = Env.get_init_var_map env2 in
  let var_fmt1 = fun v -> Format.sprintf "%s_orig" (Var.name v) in
  let var_fmt2 = fun v -> Format.sprintf "%s_mod" (Var.name v) in
  let init_fmt1 = fun v -> Format.sprintf "init_%s_orig" (Var.name v) in
  let init_fmt2 = fun v -> Format.sprintf "init_%s_mod" (Var.name v) in
  let maps = [var_map1; var_map2; init_var_map1; init_var_map2] in
  let fmts = [var_fmt1; var_fmt2; init_fmt1; init_fmt2] in
  let names = List.zip_exn maps fmts in
  let to_z3_name token =
    List.find_map names ~f:(fun (map, fmt) -> get_z3_name map token fmt)
    |> Base.Option.map ~f:Expr.to_string |> Option.value ~default:token
  in
  let smtlib_str =
    smtlib_str
    |> tokenize
    |> List.map ~f:to_z3_name
    |> build_str
  in
  info "New smtlib string: %s \n" smtlib_str;
  let declsym1 = get_decls_and_symbols env1 in
  let declsym2 = get_decls_and_symbols env2 in
  let declsym = declsym1 @ declsym2 in
  let ctx = Env.get_context env1 in
  mk_smtlib2 ctx smtlib_str declsym
  
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
