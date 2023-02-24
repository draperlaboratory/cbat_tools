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

(* SexpLib unfortunately uses # as an comment delimitter.
   We replace it with a special token and revert this after parsing. *)
let pound_token : string = "MYSPECIALPOUND682"

let remove_pound (s : string) : string =
  String.substr_replace_all s ~pattern:"#" ~with_:pound_token

let add_pound (s : string) : string =
  String.substr_replace_all s ~pattern:pound_token ~with_:"#"

let get_decls_and_symbols (env : Env.t) : ((FuncDecl.func_decl * Symbol.symbol) list) =
  let ctx = Env.get_context env in
  let var_to_decl ~key:_ ~data:z3_var decls =
    assert (Expr.is_const z3_var);
    (* "|" is a quotation character Z3 inserts we want stripped. *)
    let var_name = String.strip ~drop:(fun c -> Char.(c = '|')) (Expr.to_string z3_var) in
    let decl = FuncDecl.mk_const_decl_s ctx var_name (Expr.get_sort z3_var) in
    let sym =  Symbol.mk_string ctx var_name in
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
let mk_smtlib2 ?(name = None) (ctx : Z3.context) (smtlib_str : string)
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
          let goal_name =
            match name with
            | Some name -> name
            | None -> Expr.to_string e
          in
          e
          |> Constr.mk_goal goal_name
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
let mk_smtlib2_compare ?(name = None) (env1 : Env.t) (env2 : Env.t)
    (smtlib_str : string) : Constr.t =
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
  mk_smtlib2 ~name ctx smtlib_str declsym

let mk_smtlib2_single_with_vars
      ?(name = None) (env : Env.t) (smt_post : string)
    : Constr.t * string list * string list =
  let var_map = Env.get_var_map env in
  let init_var_map = Env.get_init_var_map env in
  let tokens = tokenize smt_post in

  (* Here we are replacing variables in the user's provided input with the
     appropriate z3 variable name.  We also save these variables for user
     by the caller. *)
  let (tokens,pre_vars,post_vars) =
    List.fold_right tokens ~init:([],[],[]) ~f:(fun t (ts,pre_v,post_v) ->
        match get_z3_name var_map t Var.name with
        | Some n -> (Expr.to_string n :: ts, pre_v, t :: post_v)
        | None ->
          begin
            match get_z3_name init_var_map t
                    (fun v -> "init_" ^ Var.name v) with
            | Some n -> (Expr.to_string n :: ts, t :: pre_v, post_v)
            | None -> (t :: ts, pre_v, post_v)
          end)
  in

  let smt_post = build_str tokens in
  info "New smt-lib string : %s\n" smt_post;
  let decl_syms = get_decls_and_symbols env in
  let ctx = Env.get_context env in
  (mk_smtlib2 ~name ctx smt_post decl_syms, pre_vars, post_vars)

let mk_smtlib2_single ?(name = None) (env : Env.t) (smt_post : string)
    : Constr.t =
  let (c,_,_) = mk_smtlib2_single_with_vars ~name:name env smt_post in c


(** [mk_and] is a slightly optimized version of [Bool.mk_and] that does not produce an
    [and] node if the number of operands is less than 2. This may improve sharing,
    but also improves compatibility of smtlib2 expressions with other solvers  *)
let mk_and (ctx : Z3.context) (xs : Constr.z3_expr list) : Constr.z3_expr =
  match xs with
  | []  -> Bool.mk_true ctx
  | [x] -> x
  | _   -> Bool.mk_and ctx xs

let process_lambda
    (varname : string)
    (model_val : Sexp.t)
    (ks : Sexp.t)
    (vs : Sexp.t) : Sexp.t =
  let rec aux acc = function
    | Sexp.List [
        Atom "ite";
        List [Atom "="; Atom x; Atom _ as k];
        Atom _ as v;
        rest
      ] when String.(x = varname) ->
      aux ((k, v) :: acc) rest
    | Atom _ as d -> acc, d
    | x ->
      failwithf "Unexpected form %s when processing lambda"
        (Sexp.to_string x |> add_pound) () in
  let m, default = aux [] model_val in
  List.fold m ~f:(fun acc (k, v) -> List [Atom "store"; acc; k; v])
    ~init:(Sexp.List [
        List [Atom "as"; Atom "const"; List [Atom "Array"; ks; vs]];
        default
      ])

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
      (assert (= mem0
        (store
          (store
            (store ((as const (Array (_ BitVec 64) (_ BitVec 8))) #b00000000)
              #b0000000000000000000000000000000000111111110000000000000000000110 #b11111111)
            #b0000000000000000000000000000000000111111110000000000000000000101 #b11111111)
        #b0000000000000000000000000000000000000000000111111111111111111111 #b00101111)))
    ] *)

let asserts_of_model (model_string : string) (sym_names : string list) : Sexp.t list =
  let process_decl l = match l with
    | Sexp.List [Sexp.Atom "define-fun"; Sexp.Atom varname; args; sort; model_val] ->
      (* If variable is not in sym_names, z3 will crash on processing it.
         Z3 can fill in gaps in the model via it's own smt search.
         The main cost is slowdown. *)
      if List.mem sym_names varname ~equal:String.equal then
        let model_val = match args with
          | Sexp.List [] -> (* Constant case *)
            model_val
          | Sexp.List [List [Atom x; s]] -> (* Function model *)
            process_lambda x model_val s sort
          | Sexp.List _ as l ->
            failwithf "model_string: %s\n\
                       function asserts_of_model: \
                       Unexpected list %s in external model\n"
              model_string (Sexp.to_string l) ()
          | Sexp.Atom a ->
            failwithf "model_string: %s\n\
                       function asserts_of_model: \
                       Unexpected atom %s in external model\n"
              model_string a () in
        Sexp.List [
          Sexp.Atom "assert";
          Sexp.List [
            Sexp.Atom "=";
            Sexp.Atom varname;
            model_val;
          ];
        ]
      else begin
        warning "Warning: %s not instantiated in Z3 query\n" varname;
        Sexp.List [Sexp.Atom "assert"; Sexp.Atom "true"]
      end
    | bad_sexp ->
      failwithf "model_string: %s\n\
                 function asserts_of_model: \
                 Unexpected form %s in external smt model\n"
        model_string (Sexp.to_string bad_sexp) () in
  let model_sexp = Sexp.of_string model_string in
  match model_sexp with
  | Sexp.List (Sexp.Atom "model" :: t) | Sexp.List t ->
    List.map ~f:process_decl t
  | Atom a ->
    failwithf "model_string: %s\n\
               function asserts_of_model: \
               Unexpected outer atom %s in external smt model\n"
      model_string a ()

(* We are still missing some funcdecls, particularly function return values *)
(** [check_external] invokes an external smt solver as a process. It communicates to the
    process via a fairly rigid interpretation of the smtlib2 protocol. It extracts the
    smtlib2 query string from the given z3_solver, queries the external solver, receives
    a counter model if SAT. It then asserts this model back to the z3_solver, which should
    check quickly. This solver can then be used with the regular cbat z3 model
    interpretation machinery. Tested with Boolector, results with other solvers may vary.*)

let check_external
    ?(print_constr = [])
    ?(fmt = Format.err_formatter)
    (solver : Z3.Solver.solver)
    (solver_path : string)
    (ctx : Z3.context)
    (declsyms : (Z3.FuncDecl.func_decl * Z3.Symbol.symbol) list) : Z3.Solver.status =
  let smt_string = Z3.Solver.to_string solver in
  let smt_preamble = "(set-logic QF_AUFBV) (set-option :produce-models true)" in
  let smt_postamble = "(check-sat) (get-model) (exit)" in
  (* Todo: Forward verbose flags to external solver? *)
  let tmp_file, chan = Stdlib.Filename.open_temp_file "wp" ".smt2" in
  (* Send query to solver *)
  Out_channel.output_string chan smt_preamble;
  Out_channel.output_string chan smt_string;
  Out_channel.output_string chan smt_postamble;
  Out_channel.flush chan;
  Out_channel.close chan;
  let cmd = sprintf "%s %s" solver_path tmp_file in
  let solver_stdout, solver_stdin = Caml_unix.open_process cmd in
  if Utils.print_diagnostics print_constr then begin
    Format.fprintf fmt "Created temp file %s\n%!" tmp_file;
    Format.fprintf fmt "Running external solver %s\n%!" solver_path
  end;
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
      failwithf "External smt model returns unsat for Z3: \n  \
                 Old_query: %s \n  \
                 Model : %s \n  \
                 Asserts: %s \n  \
                 New query :%s \n"
        smt_string
        (String.concat ~sep:"\n" smt_asserts)
        (Z3.Solver.to_string solver)
        (model_string) ()
    | Z3.Solver.UNKNOWN -> failwith "External smt model returns unknown for Z3"
  in
  let status =
    if String.(result = "unsat") then (* Regexp it? *)
      Z3.Solver.UNSATISFIABLE
    else if String.(result = "sat") then begin
      process_sat ();
      Z3.Solver.SATISFIABLE
    end else if String.(result = "unknown") then
      Z3.Solver.UNKNOWN
    else
      let unknown_output = In_channel.input_all solver_stdout in
      failwithf "Unidentified external solver %s output : %s\n%s "
        solver_path result unknown_output () in
  In_channel.close solver_stdout;
  Out_channel.close solver_stdin;
  status
