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
    (decl,sym)::decls
  in
  let var_map = Env.get_var_map env in
  let init_var_map = Env.get_init_var_map env in
  let var_decls = Env.EnvMap.fold var_map ~init:[] ~f:var_to_decl in
  Env.EnvMap.fold init_var_map ~init:var_decls ~f:var_to_decl

let mk_smtlib2 (ctx : Z3.context) (smtlib_str : string) (decl_syms : (Z3.FuncDecl.func_decl * Z3.Symbol.symbol) list) : Constr.t =
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
        if Re.Group.nb_groups g <> 1 then
          failwith "Number of groups in string delimeter is not 1"
        else
          Re.Group.get g 0)

let replace (name : string) (z3_name : string) (tokens : string list) : string list =
  List.map tokens ~f:(fun token ->
      if String.equal name token then
        z3_name
      else
        token)

let mk_smtlib2_single (env : Env.t) (smt_post : string) : Constr.t =
  let var_map = Env.get_var_map env in
  let init_var_map = Env.get_init_var_map env in
  let smt_post = Env.EnvMap.fold var_map ~init:(tokenize smt_post)
      ~f:(fun ~key:var ~data:z3_var tokens ->
          let name = Var.name var in
          let z3_name = Expr.to_string z3_var in
          replace name z3_name tokens)
  in
  let smt_post = Env.EnvMap.fold init_var_map ~init:smt_post
      ~f:(fun ~key:v ~data:init_var tokens ->
          let name = "init_" ^ (Var.name v) in
          let z3_name = Expr.to_string init_var in
          replace name z3_name tokens)
  in
  let smt_post = List.fold smt_post ~init:"" ~f:(fun post token -> token ^ post) in
  info "New smt-lib string : %s\n" smt_post;
  let decl_syms = get_decls_and_symbols env in
  let ctx = Env.get_context env in
  mk_smtlib2 ctx smt_post decl_syms

