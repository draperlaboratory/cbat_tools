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

(* FIXME: can we remove this include? *)
include Self()

module Comp = Compare
module Pre = Precondition
module Env = Environment
module Constr = Constraint
module Params = Run_parameters

(** The available options to be set. Each flag corresponds to a parameter in
    the set with the BAP custom command line. *)
type params = Params.t

let spec_of_name (no_chaos : string list) (name : string)
  : Sub.t -> Theory.target -> Env.fun_spec option =
  match name with
  | "verifier-error" -> Pre.spec_verifier_error
  | "verifier-assume" -> Pre.spec_verifier_assume
  | "verifier-nondet" -> Pre.spec_verifier_nondet no_chaos
  | "afl-maybe-log" -> Pre.spec_afl_maybe_log
  | "arg-terms" -> Pre.spec_arg_terms
  | "chaos-caller-saved" -> Pre.spec_chaos_caller_saved
  | "chaos-rax" -> Pre.spec_chaos_rax
  | "rax-out" -> Pre.spec_rax_out
  | "empty" -> Pre.spec_empty
  | name ->
    (* TODO: We should return an error here instead of failing directly, but
       that would require some code cleanup on the analysis side. *)
    let err = Printf.sprintf "'%s' is not a supported spec. See `bap wp \
                              --help' for available function specs.%!" name in
    failwith err

(* Updates the stack's base/size based on the user's input. *)
let update_stack ~(base : int option) ~(size : int option) : Env.mem_range =
  let update_base stack_base range =
    match stack_base with
    | None -> range
    | Some base -> Env.update_stack_base range base in
  let update_size stack_size range =
    match stack_size with
    | None -> range
    | Some size -> Env.update_stack_size range size in
  Pre.default_stack_range
  |> update_base base
  |> update_size size

let update_default_num_unroll (num : int option) : unit =
  match num with
  | Some n -> Pre.num_unroll := n
  | None -> ()

(* Creates a map of modified subroutine names to original subroutine names
   based off the regex from the user. *)
let mk_func_name_map
    ~orig:(subs_orig : Sub.t Seq.t)
    ~modif:(subs_mod : Sub.t Seq.t)
    (re : (string * string) list)
  : string String.Map.t =
  let re = List.rev re in
  Seq.fold subs_orig ~init:String.Map.empty ~f:(fun map sub_orig ->
      let name_orig = Sub.name sub_orig in
      List.fold re ~init:map ~f:(fun m (orig, modif) ->
          let regexp = Str.regexp orig in
          let name_mod = Str.replace_first regexp modif name_orig in
          let in_orig = Str.string_match regexp name_orig 0 in
          let in_mod = Seq.exists subs_mod ~f:(fun s ->
              String.equal (Sub.name s) name_mod) in
          if in_orig && in_mod then
            String.Map.set m ~key:name_mod ~data:name_orig
          else
            m))

(* Checks the user's input for outputting a gdb script. *)
let output_to_gdb ~(filename : string option) ~(func : string)
    (solver : Z3.Solver.solver) (status : Z3.Solver.status) (env : Env.t)
  : unit =
  match filename with
  | None -> ()
  | Some name -> Output.output_gdb ~filename:name ~func solver status env

(* Checks the user's input for outputting a bildb script. *)
let output_to_bildb ~(filename : string option) (solver : Z3.Solver.solver)
    (status : Z3.Solver.status) (env : Env.t) : unit =
  match filename with
  | None -> ()
  | Some name -> Output.output_bildb solver status env name

(* Contains information about the precondition and the subroutines from
   the analysis to be printed out. *)
type combined_pre =
  | Single of {
      pre : Constr.t;
      orig : sub Comp.code
    }
  | Comparative of {
      pre : Constr.t;
      orig : sub Comp.code;
      modif : sub Comp.code
    }

(* If an offset is specified, generates a function of the address of a memory
   read in the original binary to the address plus an offset in the modified
   binary. *)
let get_mem_offsets (ctx : Z3.context) (p : params) (syms_orig : Symbol.t list)
    (syms_mod : Symbol.t list) : Constr.z3_expr -> Constr.z3_expr =
  if p.mem_offset then
    Symbol.offset_constraint ~orig:syms_orig ~modif:syms_mod ctx
  else
    fun addr -> addr

(* Rewrites the concrete addresses in the modified subroutine to match those
   of the original subroutine. *)
let rewrite_addresses (p : params) (syms_orig : Symbol.t list)
    (syms_mod : Symbol.t list) (sub : Sub.t) : Sub.t =
  if p.rewrite_addresses then
    Symbol.rewrite_addresses ~orig:syms_orig ~modif:syms_mod sub
  else
    sub

(* Generate the exp_conds for the original binary based on the flags passed in
   from the CLI. Generating the memory offsets requires the environment of
   the modified binary. *)
let exp_conds_orig (p : params) (env_mod : Env.t) (syms_orig : Symbol.t list)
    (syms_mod : Symbol.t list) (mem_orig : value memmap)
    (mem_mod : value memmap) : Env.exp_cond list =
  let ctx = Env.get_context env_mod in
  let offsets =
    (* We shouldn't assume that memory is equivalent at an offset when the
       init-mem flag is used since this flag checks the values in the rodata
       section. *)
    let offsets = get_mem_offsets ctx p syms_orig syms_mod in
    let init_mem = Pre.init_mem_range ctx p.init_mem mem_orig mem_mod in
    [Pre.mem_read_offsets env_mod ~init_mem ~offsets]
  in
  let null_derefs =
    if p.check_null_derefs then
      [Pre.non_null_load_assert; Pre.non_null_store_assert]
    else []
  in
  let invalid_derefs =
    if p.check_invalid_derefs then
      [Pre.valid_load_assert; Pre.valid_store_assert]
    else []
  in
  List.concat [offsets; null_derefs; invalid_derefs]

(* Generate the exp_conds for the modified binary based on the flags passed in
   from the CLI. *)
let exp_conds_mod (p : params) : Env.exp_cond list =
  let null_derefs =
    if p.check_null_derefs then
      [Pre.non_null_load_vc; Pre.non_null_store_vc]
    else []
  in
  let invalid_derefs =
    if p.check_invalid_derefs then
      [Pre.valid_load_vc; Pre.valid_store_vc]
    else []
  in
  null_derefs @ invalid_derefs

(* Parse a single user_func_spec string to make a func_spec. *)
let parse_user_func_spec (user_func_spec: string * string * string) : (Sub.t -> Theory.target -> Env.fun_spec option) =
  match user_func_spec with
    (name,pre,post) ->
    let name = Caml.String.trim name in
    info "Making spec from %s %s %s" name pre post;
    Pre.user_func_spec ~sub_name:name ~sub_pre:pre ~sub_post:post

(* Parse the list of specs provided by the user. *)
let parse_user_func_specs (p : params)
  :   (Sub.t -> Theory.target -> Env.fun_spec option) list
      * (Sub.t -> Theory.target -> Env.fun_spec option) list =
  let shared_specs =
    List.map p.user_func_specs ~f:parse_user_func_spec
  in
  (shared_specs @ List.map p.user_func_specs_orig ~f:parse_user_func_spec,
   shared_specs @ List.map p.user_func_specs_mod  ~f:parse_user_func_spec)

(* Determine which function specs to use in WP. *)
let fun_specs ~orig:(orig : bool) (p : params) (to_inline : Sub.t Seq.t)
  : (Sub.t -> Theory.target -> Env.fun_spec option) list =
  let default = [
    Pre.spec_verifier_assume;
    Pre.spec_verifier_nondet p.no_chaos;
    Pre.spec_empty;
    Pre.spec_chaos_caller_saved
  ] in
  let user_func_spec =
    (if orig then fst else snd) @@ parse_user_func_specs p
  in
  let trip_asserts = if p.trip_asserts then [Pre.spec_verifier_error] else [] in
  let inline = [Pre.spec_inline to_inline] in
  let specs =
    if List.is_empty p.fun_specs then
      default
    else
      List.map p.fun_specs ~f:(spec_of_name p.no_chaos)
  in
  user_func_spec @ trip_asserts @ inline @ specs

(* If the compare_func_calls flag is set, add the property for comparative
   analysis. *)
let func_calls (flag : bool) : (Comp.comparator * Comp.comparator) option =
  if flag then
    Some Comp.compare_subs_fun
  else
    None

(* If the user specifies registers' post values to compare, add the property:
   if all registers between the two binaries are equal to each other at the
   beginning of a subroutine's execution, the specified registers should have
   the same post values. *)
let post_reg_values
    ~orig:({prog=sub1; env=env1; _} : sub Comp.code)
    ~modif:({prog=sub2; env=env2; _} : sub Comp.code)
    (reg_names : string list)
  : (Comp.comparator * Comp.comparator) option =
  if List.is_empty reg_names then
    None
  else begin
    let all_regs = Var.Set.union
        (Pre.get_vars env1 sub1) (Pre.get_vars env2 sub2) in
    let post_regs = Var.Set.union
        (Pre.set_of_reg_names env1 sub1 reg_names)
        (Pre.set_of_reg_names env2 sub2 reg_names) in
    debug "Pre register vals: %s%!" (Utils.varset_to_string all_regs);
    debug "Post register vals: %s%!" (Utils.varset_to_string post_regs);
    Some (Comp.compare_subs_eq ~pre_regs:all_regs ~post_regs:post_regs)
  end

(* Parses the user's smtlib queries for use in comparative analysis. *)
let smtlib
    ~precond:(precond : string)
    ~postcond:(postcond : string)
  : (Comp.comparator * Comp.comparator) option =
  if String.is_empty precond && String.is_empty postcond then
    None
  else
    Some (Comp.compare_subs_smtlib ~smtlib_hyp:precond ~smtlib_post:postcond)

(* obtain a set of general purpose registers
 * based on their string names and architecture. *)
let create_vars (l : string list) (env : Env.t) : Bap.Std.Var.Set.t =
  let gprs = Env.get_gprs env
  in
  List.map l
    ~f:(fun var_name ->
        let var = Bap.Std.Var.Set.find gprs
            ~f:(fun var -> String.equal var_name (Var.name var)) in
        match var with
        | Some r -> r
        | None ->
          Printf.sprintf
            "Could not find %s in the set of general purpose registers"
            var_name
          |> failwith
      )
  |> Bap.Std.Var.Set.of_list

(* Returns a set of comparators that provide the constraint that
   the pointer registers are treated as pointers. *)
let gen_pointer_flag_comparators
    (l : string list)
    (env1 : Env.t)
    (env2 : Env.t)
    (pointer_env1_vars : Var.t List.t)
    (pointer_env2_vars : Var.t List.t)
  : (Comp.comparator * Comp.comparator) option =
  if List.length l = 0 then None
  else
    let regs_orig = List.filter_map pointer_env1_vars ~f:(fun var -> Env.get_init_var env1 var) in
    let regs_mod = List.filter_map pointer_env2_vars ~f:(fun var -> Env.get_init_var env2 var) in
    let pre_conds = Pre.construct_pointer_constraint regs_orig env1
        (Some regs_mod) (Some env2) in
    let ctx = Env.get_context env1 in
    let post_conds = Constr.trivial ctx in
    Some (Comp.compare_subs_constraints ~pre_conds ~post_conds)

(* If we are rewriting addresses, we can equate the two memory arrays. *)
let mem_eq (rewrite_addrs : bool) : (Comp.comparator * Comp.comparator) option =
  if rewrite_addrs then
    Some Compare.compare_subs_mem_eq
  else
    None

let mem_init (mem_init : bool) : (Comp.comparator * Comp.comparator) option =
  if mem_init then
    Some Compare.compare_subs_mem_init
  else
    None

(* Returns a list of postconditions and a list of hypotheses based on the
   flags set from the command line. *)
let comparators_of_flags
    ~orig:(code1 : sub Comp.code)
    ~modif:(code2 : sub Comp.code)
    (p : params)
    (pointer_env1_vars : Var.t List.t)
    (pointer_env2_vars : Var.t List.t)
  : Comp.comparator list * Comp.comparator list =
  let comps =
    [
      Some Comp.compare_subs_sp;

      func_calls p.compare_func_calls;

      post_reg_values p.compare_post_reg_values
        ~orig:code1 ~modif:code2;

      smtlib ~precond:p.precond ~postcond:p.postcond;

      gen_pointer_flag_comparators p.pointer_reg_list
        code1.env code2.env pointer_env1_vars pointer_env2_vars;

      mem_eq p.rewrite_addresses;

      mem_init p.init_mem;
    ] |>
    List.filter_opt
  in
  let comps =
    if List.is_empty comps then
      [Comp.compare_subs_empty_post]
    else
      comps
  in
  List.unzip comps

(* Runs a single binary analysis. *)
let single
    (z3_ctx : Z3.context)
    (var_gen : Env.var_gen)
    (p : params)
    (prog : program term)
    (code_addrs : Utils.Code_addrs.t)
    (mem : value memmap)
    (target : Theory.target)
    (_file : string)
  : combined_pre =
  let subs = Term.enum sub_t prog in
  let main_sub = Utils.find_func_err subs p.func in
  let to_inline = Utils.match_inline p.inline subs in
  let specs = fun_specs ~orig:true p to_inline in
  let exp_conds = exp_conds_mod p in
  let stack_range = update_stack ~base:p.stack_base ~size:p.stack_size in
  let loop_invariant =
    Params.parse_loop_invariant p.loop_invariant target main_sub
    |> Pre.loop_invariant_checker
  in
  let env =
    Pre.mk_env
      z3_ctx
      var_gen
      ~subs
      ~target
      ~specs
      ~smtlib_compat:(Option.is_some p.ext_solver_path)
      ~use_fun_input_regs:p.use_fun_input_regs
      ~exp_conds
      ~stack_range
      ~loop_handlers:[loop_invariant]
  in
  let true_constr = Constr.trivial z3_ctx in
  let vars = Pre.get_vars env main_sub in
  let vars_pointer_reg = create_vars p.pointer_reg_list env in
  let hyps, env = Pre.init_vars (Var.Set.union vars vars_pointer_reg) env in
  let hyps = (Pre.set_sp_range env) :: hyps in
  let hyps =
    (* short circuit to avoid extraneous "&& true" constraint *)
    if List.length p.pointer_reg_list > 0
    then
      let z3_exprs = List.filter_map (Bap.Std.Var.Set.to_list vars_pointer_reg)
          ~f:(fun var -> Env.get_init_var env var) in
      (Pre.construct_pointer_constraint z3_exprs env None None) :: hyps
    else hyps in
  let init_mem_hyps, env =
    (* FIXME: check p.init_mem here *)
    if p.init_mem then
      Pre.init_mem env mem code_addrs
    else
      [], env
  in
  let hyps = init_mem_hyps @ hyps in
  let post =
    if String.is_empty p.postcond then
      true_constr
    else
      Z3_utils.mk_smtlib2_single
        ~name:(Some "Custom postcondition") env p.postcond
  in
  let pre, env = Pre.visit_sub env post main_sub in
  let precond_from_flag = Z3_utils.mk_smtlib2_single
      ~name:(Some "Custom precondition") env p.precond in
  let pre = Constr.mk_clause [precond_from_flag;] [pre] in
  let pre = Constr.mk_clause hyps [pre] in
  if List.mem p.show "bir" ~equal:String.equal then
    Printf.printf "\nSub:\n%s\n%!" (Sub.to_string main_sub);
  Single {
    pre;
    orig = Comp.{
        env;
        prog = main_sub;
        mem;
        code_addrs;
      }
  }

(* Runs a comparative analysis. *)
let comparative
    (z3_ctx : Z3.context)
    (var_gen : Env.var_gen)
    (p : params)
    (prog1 : program term)
    (code1 : Utils.Code_addrs.t)
    (mem1 : value memmap)
    (target1 : Theory.target)
    (file1 : string)
    (prog2 : program term)
    (code2 : Utils.Code_addrs.t)
    (mem2 : value memmap)
    (target2 : Theory.target)
    (file2 : string)
  : combined_pre =
  let syms1 = Symbol.get_symbols file1 in
  let syms2 = Symbol.get_symbols file2 in
  let subs1 = Term.enum sub_t prog1 in
  let subs2 = Term.enum sub_t prog2 in
  let main_sub1 = Utils.find_func_err subs1 p.func in
  let main_sub2 =
    Utils.get_mod_func_name p.func_name_map p.func
    |> Option.value ~default:p.func
    |> Utils.find_func_err subs2
    |> rewrite_addresses p syms1 syms2
  in
  let stack_range = update_stack ~base:p.stack_base ~size:p.stack_size in
  let env2, pointer_vars_2 =
    let to_inline2 = Utils.match_inline p.inline subs2 in
    let specs2 = fun_specs ~orig:false p to_inline2 in
    let exp_conds2 = exp_conds_mod p in
    let func_name_map =
      mk_func_name_map ~orig:subs1 ~modif:subs2 p.func_name_map in
    let env2 = Pre.mk_env z3_ctx var_gen
        ~subs:subs2
        ~target:target2
        ~specs:specs2
        ~smtlib_compat:(Option.is_some p.ext_solver_path)
        ~use_fun_input_regs:p.use_fun_input_regs
        ~exp_conds:exp_conds2
        ~stack_range
        ~func_name_map
    in
    let env2 = Env.set_freshen env2 true in
    let vars_sub = Pre.get_vars env2 main_sub2 in
    let vars_pointer_reg = create_vars p.pointer_reg_list env2 in
    let _, env2 = Pre.init_vars (Var.Set.union vars_sub vars_pointer_reg) env2 in
    env2, vars_pointer_reg
  in
  let env1, pointer_vars_1 =
    let to_inline1 = Utils.match_inline p.inline subs1 in
    let specs1 = fun_specs ~orig:true p to_inline1 in
    let exp_conds1 = exp_conds_orig p env2 syms1 syms2 mem1 mem2 in
    let env1 = Pre.mk_env z3_ctx var_gen
        ~subs:subs1
        ~target:target1
        ~specs:specs1
        ~smtlib_compat:(Option.is_some p.ext_solver_path)
        ~use_fun_input_regs:p.use_fun_input_regs
        ~exp_conds:exp_conds1
        ~stack_range
    in
    let vars_sub = Pre.get_vars env1 main_sub1 in
    let vars_pointer_reg = create_vars p.pointer_reg_list env1 in
    let _, env1 = Pre.init_vars (Var.Set.union vars_sub vars_pointer_reg) env1 in
    (*(Bap.Std.Var.Set.union vars_sub vars_pointer_reg |> Bap.Std.Var.Set.union sp) env1 in*)
    env1, vars_pointer_reg
  in
  let code1 = Comp.{prog = main_sub1; env = env1; mem = mem1; code_addrs = code1} in
  let code2 = Comp.{prog = main_sub2; env = env2; mem = mem2; code_addrs = code2} in
  let posts, hyps =
    comparators_of_flags ~orig:code1 ~modif:code2 p
      (pointer_vars_1 |> Bap.Std.Var.Set.to_list)
      (pointer_vars_2 |> Bap.Std.Var.Set.to_list)
  in
  let pre, env1, env2 =
    Comp.compare_subs ~postconds:posts ~hyps:hyps
      ~original:code1 ~modified:code2
  in
  let code1 = {code1 with env=env1} in
  let code2 = {code2 with env=env2} in
  if List.mem p.show "bir" ~equal:String.equal then
    Printf.printf "\nComparing\n\n%s\nand\n\n%s\n%!"
      (Sub.to_string main_sub1) (Sub.to_string main_sub2);
  Comparative { pre = pre; orig = code1; modif = code2 }

let check_pre (p : params) (ctx : Z3.context) (cp : combined_pre)
  : (Z3.Solver.status, 'a) result =
  let solver = Z3.Solver.mk_solver ctx None in
  let pre = match cp with
    | Single cp -> cp.pre
    | Comparative cp -> cp.pre
  in
  if (List.mem p.debug "constraint-stats" ~equal:(String.equal)) then
    Constr.print_stats pre;
  let debug_eval =
    (List.mem p.debug "eval-constraint-stats" ~equal:(String.equal)) in
  let result = match p.ext_solver_path with
    | None -> Pre.check ~print_constr:p.show ~debug:debug_eval solver ctx pre
    | Some ext_solver_path ->
      let declsyms = match cp with
        | Single cp -> Z3_utils.get_decls_and_symbols cp.orig.env
        | Comparative cp ->
          let declsyms_orig = Z3_utils.get_decls_and_symbols cp.orig.env in
          let declsyms_modif = Z3_utils.get_decls_and_symbols cp.modif.env in
          List.append declsyms_orig declsyms_modif
      in
      Pre.check
        ~print_constr:p.show
        ~debug:debug_eval
        ~ext_solver:(ext_solver_path, declsyms)
        solver ctx pre
  in
  if (List.mem p.debug "z3-solver-stats" ~equal:(String.equal)) then
    Printf.printf "Showing solver statistics : \n %s \n %!"
      (Z3.Statistics.to_string (Z3.Solver.get_statistics solver));
  let env = match cp with
    | Single cp -> cp.orig.env
    | Comparative cp -> cp.modif.env
  in
  output_to_gdb ~filename:p.gdb_output ~func:p.func solver result env;
  output_to_bildb ~filename:p.bildb_output solver result env;
  let () = match cp with
    | Single cp ->
      Output.print_result solver result cp.pre ~orig:cp.orig
        ~modif:cp.orig ~show:p.show;
    | Comparative cp ->
      Output.print_result solver result cp.pre ~orig:cp.orig
        ~modif:cp.modif ~show:p.show;
  in
  Ok result


(* Error for when the user specifies 0 or more than 2 files to analyze. *)
type Bap_main.Extension.Error.t += Unsupported_file_count of string


type input =
  {
    program : program term;
    code_addrs : Utils.Code_addrs.t;
    target : Theory.target;
    filename : string;
  }

(* Entrypoint for the WP analysis. *)
let run
    (p : params)
    (files : input list)
  : (Z3.Solver.status, Bap_main.error) result =
  if (List.mem p.debug "z3-verbose"  ~equal:(String.equal)) then
    Z3.set_global_param "verbose" "10";
  let z3_ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  update_default_num_unroll p.num_unroll;
  (* Determine whether to perform a single or comparative analysis. *)
  match files with
  | [input] ->
    let {program = prog; code_addrs; target = tgt; filename = file} = input in
    let mem = Utils.init_mem ~ogre:p.ogre ~init_mem:p.init_mem file in
    single z3_ctx var_gen p prog code_addrs mem tgt file
    |> check_pre p z3_ctx
  | [input1; input2] ->
    let {
      program = prog1;
      code_addrs = code1;
      target = tgt1;
      filename = file1
    } = input1 in
    let {
      program = prog2;
      code_addrs = code2;
      target = tgt2;
      filename = file2
    } = input2 in
    let ogre1, ogre2 = match p.ogre with
      | Some _ -> p.ogre, p.ogre
      | None -> p.ogre_orig, p.ogre_mod in
    let mem1 = Utils.init_mem ~ogre:ogre1 ~init_mem:p.init_mem file1 in
    let mem2 = Utils.init_mem ~ogre:ogre2 ~init_mem:p.init_mem file2 in
    comparative
      z3_ctx var_gen p
      prog1 code1 mem1 tgt1 file1
      prog2 code2 mem2 tgt2 file2
    |> check_pre p z3_ctx
  | _ ->
    let err =
      Printf.sprintf "WP can only analyze one binary for a single analysis or \
                      two binaries for a comparative analysis. Number of \
                      binaries provided: %d.%!" (List.length files) in
    Error (Unsupported_file_count err)
