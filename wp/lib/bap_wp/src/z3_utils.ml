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
        (Expr.to_string z3_var |> (String.strip ~drop:(fun c -> Char.(c = '|'))))
        (Expr.get_sort z3_var) in
    let sym =  Symbol.mk_string ctx (Expr.to_string z3_var |> (String.strip ~drop:(fun c -> Char.(c = '|')))) in
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
  : (Constr.z3_expr option) =
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


(** [mk_and] is a slightly optimized version of [Bool.mk_and] that does not produce an
    [and] node if the number of operands is less than 2. This may improve sharing,
    but also improves compatibility of smtlib2 expressions with other solvers  *)
let mk_and ( ctx : Z3.context ) (xs : Constr.z3_expr list) : Constr.z3_expr =
  match xs with
  | []  -> Bool.mk_true ctx
  | [x] -> x
  | _   -> Bool.mk_and ctx xs


(** [asserts_of_model] takes a string of an smtlib2 model returned by an external solver and 
    processes it into an equivalent list of assert strings.

    The models are expected to be of the form

    (model
      (define-fun strlen_ret_RAX () (_ BitVec 64) #b0000000000000000000000000000000000100100110000000000000000000000)
      (define-fun RSP0 () (_ BitVec 64) #b0000000000000000000000000000000000111111110000000000000000000101)
      (define-fun RBX0 () (_ BitVec 64) #b0010111100101110111111110010111100101101111111111111111111111111)
      (define-fun mem0 (
      (mem0_x0 (_ BitVec 64))) (_ BitVec 8)
        (ite (= mem0_x0 #b0000000000000000000000000000000000000000000111111111111111111111) #b00101111
        (ite (= mem0_x0 #b0000000000000000000000000000000000111111110000000000000000000101) #b11111111
        (ite (= mem0_x0 #b0000000000000000000000000000000000111111110000000000000000000110) #b11111111
          #b00000000)))))))))))))))))))
    )

    This is processed via parsing as an S-expression into assert strings of the form

    [
      (assert (= strlen_ret_RAX #b0000000000000000000000000000000000100100110000000000000000000000)) ;
      (assert (= RSP0 #b0000000000000000000000000000000000111111110000000000000000000101)) ;
      (assert (= RBX0 #b0010111100101110111111110010111100101101111111111111111111111111)) ;
      (assert (= mem0 (lambda (
      (mem0_x0 (_ BitVec 64)))
        (ite (= mem0_x0 #b0000000000000000000000000000000000000000000111111111111111111111) #b00101111
        (ite (= mem0_x0 #b0000000000000000000000000000000000111111110000000000000000000101) #b11111111
        (ite (= mem0_x0 #b0000000000000000000000000000000000111111110000000000000000000110) #b11111111
          #b00000000))))))))))))))))))))
    ] *)

let asserts_of_model (model_string : string) (sym_names : string list) : Sexp.t list =
  let process_decl l = match l with
    | Sexp.List [Sexp.Atom "define-fun" ; Sexp.Atom varname; args ; _ ; model_val ] ->
      (* If variable is not in sym_names, z3 will crash on processing it.
         Z3 can fill in gaps in the model via it's own smt search.
         The main cost is slowdown. *)
      if (List.mem sym_names varname ~equal:String.equal)
      then
        let model_val = match args with
          | Sexp.List [] ->  (* Constant case *)
            model_val
          | Sexp.List _  ->  (* Function model *)
            Sexp.List [Sexp.Atom "lambda" ; args; model_val] (* Sexp.Atom varname *)
          | Sexp.Atom _ -> failwith "Unexpected atom"
        in
        Sexp.List [Sexp.Atom "assert" ;
                   Sexp.List [Sexp.Atom "=" ; Sexp.Atom varname ; model_val]]
      else
        begin
          Printf.printf "Warning: %s not instantiated in Z3 query\n" varname;
          Sexp.List [Sexp.Atom "assert" ; Sexp.Atom "true"]
        end
    | _ -> failwith "Error: Unexpected form in external smt model"
  in
  let model_sexp = Sexp.of_string model_string in
  match model_sexp with
  | Sexp.List (Sexp.Atom "model" :: t) ->
    List.map ~f:process_decl t
  | _ -> failwith "Error: Unexpected form in external smt model"

(* We are still missing some funcdecls, particularly function return values *)
(** [check_external] invokes an external smt solver as a process. It communicates to the
    process via a fairly rigid interpretation of the smtlib2 protocol. It extracts the
    smtlib2 query string from the given z3_solver, queries the external solver, receives
    a counter model if SAT. It then asserts this model back to the z3_solver, which should
    check quickly. This solver can then be used with the regular cbat z3 model
    interpretation machinery. Tested with Boolector, results with other solvers may vary.*)

let check_external
    (solver : Z3.Solver.solver)
    (solver_path : string)
    (ctx : Z3.context)
    (declsyms : (Z3.FuncDecl.func_decl * Z3.Symbol.symbol) list) : Z3.Solver.status =
  let smt_string = Z3.Solver.to_string solver in
  let smt_preamble = "(set-logic QF_AUFBV) (set-option :produce-models true)" in
  let smt_postamble = "(check-sat) (get-model) (exit)" in
  (* Todo: Forward verbose flags to external solver? *)
  let (solver_stdout, solver_stdin) = Caml_unix.open_process solver_path in
  (* Send query to solver *)
  Out_channel.output_string solver_stdin smt_preamble;
  Out_channel.output_string solver_stdin smt_string;
  Out_channel.output_string solver_stdin smt_postamble;
  Out_channel.flush solver_stdin;
  printf "Running external solver %s\n%!" solver_path;

  (* SexpLib unfortunately uses # as an comment delimitter.
     We replace it with a special token and revert this after parsing. *)
  let pound_token = "MYSPECIALPOUND682" in
  let remove_pound s = String.substr_replace_all s ~pattern:"#" ~with_:pound_token in
  let add_pound s = String.substr_replace_all s ~pattern:pound_token ~with_:"#" in

  let result = In_channel.input_line_exn solver_stdout in
  (* Parse external model into SExp, convert into smtlib asserts,
     assert to Z3, verify that it is a model *)
  let process_sat (_ : unit) =
    let model_string = In_channel.input_all solver_stdout in
    let model_string = remove_pound model_string in
    let decls, syms = (* get_decls_and_symbols env*) declsyms |> List.unzip in
    let sym_strings = List.map ~f:(fun sym ->
      let sym_string = Z3.Symbol.to_string sym in
      if (String.contains sym_string '#')
      then "|" ^ (remove_pound sym_string) ^ "|" (* SMTlib escaping using | *)
      else sym_string) syms
    in
    let smt_asserts = asserts_of_model model_string sym_strings in
    let smt_asserts = List.map smt_asserts ~f:(fun assert_ ->
        Sexp.to_string assert_ |> add_pound) in
    List.iter smt_asserts ~f:(fun smt_assert ->
        let asts = Z3.SMT.parse_smtlib2_string ctx smt_assert [] [] syms decls  in
        Z3.Solver.add solver (Z3.AST.ASTVector.to_expr_list asts)
      );
    let res = Z3.Solver.check solver [] in
    match res with
    | Z3.Solver.SATISFIABLE -> ()
    | Z3.Solver.UNSATISFIABLE ->
      failwith (sprintf "External smt model returns unsat for Z3: \n
                           Old_query: %s \n
                           Model : %s \n
                           Asserts: %s \n
                           New query :%s \n"
                  smt_string
                  (String.concat ~sep:"\n" smt_asserts)
                  (Z3.Solver.to_string solver)
                  (model_string))
    | Z3.Solver.UNKNOWN -> failwith "External smt model returns unknown for Z3"
  in
  if String.(result = "unsat") then (* Regexp it? *)
    Z3.Solver.UNSATISFIABLE
  else if String.(result = "sat") then
    begin
      let () = process_sat () in
      Z3.Solver.SATISFIABLE
    end
  else if String.(result = "unknown") then
    Z3.Solver.UNKNOWN
  else
    begin
      let unknown_output = In_channel.input_all solver_stdout in
      failwith (sprintf "Unidentified external solver %s output : %s\n%s "
                  solver_path result unknown_output)
    end



