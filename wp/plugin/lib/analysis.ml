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
open Bap_main
open Bap.Std
open Bap_wp
open Parameters

include Self()

module Comp = Compare
module Pre = Precondition
module Env = Environment
module Constr = Constraint
module Params = Parameters

(* Error for when the user specifies 0 or more than 2 files to analyze. *)
type Extension.Error.t += Unsupported_file_count of string

(* Contains information about the precondition and the subroutines from
   the analysis to be printed out. *)
type combined_pre = {
  pre : Constr.t;
  orig : Env.t * Sub.t;
  modif : Env.t * Sub.t
}

(* If an offset is specified, generates a function of the address of a memory
   read in the original binary to the address plus an offset in the modified
   binary. *)
let get_mem_offsets (ctx : Z3.context) (p : Params.t) (file1 : string)
    (file2 : string) : Constr.z3_expr -> Constr.z3_expr =
  if p.mem_offset then
    let syms_orig = Symbol.get_symbols file1 in
    let syms_mod = Symbol.get_symbols file2 in
    Symbol.offset_constraint ~orig:syms_orig ~modif:syms_mod ctx
  else
    fun addr -> addr

(* Generate the exp_conds for the original binary based on the flags passed in
   from the CLI. Generating the memory offsets requires the environment of
   the modified binary. *)
let exp_conds_orig (p : Params.t) (env_mod : Env.t) (file1 : string)
    (file2 : string) : Env.exp_cond list =
  let ctx = Env.get_context env_mod in
  let offsets =
    get_mem_offsets ctx p file1 file2
    |> Pre.mem_read_offsets env_mod
  in
  if p.check_null_derefs then
    [Pre.non_null_load_assert; Pre.non_null_store_assert; offsets]
  else
    [offsets]

(* Generate the exp_conds for the modified binary based on the flags passed in
   from the CLI. *)
let exp_conds_mod (p : Params.t) : Env.exp_cond list =
  if p.check_null_derefs then
    [Pre.non_null_load_vc; Pre.non_null_store_vc]
  else
    []

(* Determine which function specs to use in WP. *)
let fun_specs (p : Params.t) (to_inline : Sub.t Seq.t)
  : (Sub.t -> Arch.t -> Env.fun_spec option) list =
  let default = [
    Pre.spec_verifier_assume;
    Pre.spec_verifier_nondet;
    Pre.spec_afl_maybe_log;
    Pre.spec_inline to_inline;
    Pre.spec_empty;
    Pre.spec_arg_terms;
    Pre.spec_chaos_caller_saved;
    Pre.spec_rax_out
  ] in
  if p.trip_asserts then
    Pre.spec_verifier_error :: default
  else
    default

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
    ~orig:(sub1, env1 : Sub.t * Env.t)
    ~modif:(sub2, env2 : Sub.t * Env.t)
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

(* The stack pointer hypothesis for a comparative analysis. *)
let sp (arch : Arch.t) : (Comp.comparator * Comp.comparator) option =
  match arch with
  | `x86_64 -> Some Comp.compare_subs_sp
  | _ ->
    error "WP can only generate hypotheses about the stack pointer and \
           memory for the x86_64 architecture.\n%!";
    None


(* Returns a set of comparators that provide the constraint that
   the pointer registers are treated as pointers. *)
let gen_pointer_flag_comparators
    (l: string list) (env1: Env.t) (env2: Env.t option)
  : (Comp.comparator * Comp.comparator) option =
  if List.length l = 0 then None
  else
    let pre_conds = Z3_utils.construct_pointer_constraint l env1 env2 in
    let post_conds = Env.trivial_constr env1 in
    Comp.compare_subs_constraints ~pre_conds ~post_conds |> Some


(* Returns a list of postconditions and a list of hypotheses based on the
   flags set from the command line. *)
let comparators_of_flags
    ~orig:(sub1, env1 : Sub.t * Env.t)
    ~modif:(sub2, env2 : Sub.t * Env.t)
    (p : Params.t)
  : Comp.comparator list * Comp.comparator list =
  let arch = Env.get_arch env1 in
  let comps = [
    func_calls p.compare_func_calls;
    post_reg_values p.compare_post_reg_values
      ~orig:(sub1, env1) ~modif:(sub2, env2);
    smtlib ~precond:p.precond ~postcond:p.postcond;
    sp arch;
    gen_pointer_flag_comparators p.pointer_reg_list env1 (Some env2);
  ] |> List.filter_opt
  in
  let comps =
    if List.is_empty comps then
      [Comp.compare_subs_empty_post]
    else
      comps
  in
  List.unzip comps

(* Runs a single binary analysis. *)
let single (bap_ctx : ctxt) (z3_ctx : Z3.context) (var_gen : Env.var_gen)
    (p : Params.t) (file : string) : combined_pre =
  let prog, arch = Utils.read_program bap_ctx
      ~loader:Utils.loader ~filepath:file in
  let subs = Term.enum sub_t prog in
  let main_sub = Utils.find_func_err subs p.func in
  let to_inline = Utils.match_inline p.inline subs in
  let specs = fun_specs p to_inline in
  let exp_conds = exp_conds_mod p in
  let stack_range = Utils.update_stack ~base:p.stack_base ~size:p.stack_size in
  let env = Pre.mk_env z3_ctx var_gen ~subs ~arch ~specs
      ~use_fun_input_regs:p.use_fun_input_regs ~exp_conds ~stack_range in
  let true_constr = Env.trivial_constr env in
  let hyps, env = Pre.init_vars (Pre.get_vars env main_sub) env in
  let hyps = (Pre.set_sp_range env) :: hyps in
  let hyps =
    if List.length p.pointer_reg_list > 0
    then (Z3_utils.construct_pointer_constraint p.pointer_reg_list env None) :: hyps
    else hyps in
  let post =
    if String.is_empty p.postcond then
      true_constr
    else
      Z3_utils.mk_smtlib2_single env p.postcond
  in
  let pre, env = Pre.visit_sub env post main_sub in
  let precond_from_flag = Z3_utils.mk_smtlib2_single env p.precond in
  let pre = Constr.mk_clause [precond_from_flag;] [pre] in
  let pre = Constr.mk_clause hyps [pre] in
  if List.mem p.show "bir" ~equal:String.equal then
    Printf.printf "\nSub:\n%s\n%!" (Sub.to_string main_sub);
  { pre = pre; orig = env, main_sub; modif = env, main_sub }

(* Runs a comparative analysis. *)
let comparative (bap_ctx : ctxt) (z3_ctx : Z3.context) (var_gen : Env.var_gen)
    (p : Params.t) (file1 : string) (file2 : string) : combined_pre =
  let prog1, arch1 = Utils.read_program bap_ctx
      ~loader:Utils.loader ~filepath:file1 in
  let prog2, arch2 = Utils.read_program bap_ctx
      ~loader:Utils.loader ~filepath:file2 in
  let subs1 = Term.enum sub_t prog1 in
  let subs2 = Term.enum sub_t prog2 in
  let main_sub1 = Utils.find_func_err subs1 p.func in
  let main_sub2 = Utils.find_func_err subs2 p.func in
  let stack_range = Utils.update_stack ~base:p.stack_base ~size:p.stack_size in
  let env2 =
    let to_inline2 = Utils.match_inline p.inline subs2 in
    let specs2 = fun_specs p to_inline2 in
    let exp_conds2 = exp_conds_mod p in
    let env2 = Pre.mk_env z3_ctx var_gen
        ~subs:subs2
        ~arch:arch2
        ~specs:specs2
        ~use_fun_input_regs:p.use_fun_input_regs
        ~exp_conds:exp_conds2
        ~stack_range
    in
    let env2 = Env.set_freshen env2 true in
    let _, env2 = Pre.init_vars (Pre.get_vars env2 main_sub2) env2 in
    env2
  in
  let env1 =
    let to_inline1 = Utils.match_inline p.inline subs1 in
    let specs1 = fun_specs p to_inline1 in
    let exp_conds1 = exp_conds_orig p env2 file1 file2 in
    let env1 = Pre.mk_env z3_ctx var_gen
        ~subs:subs1
        ~arch:arch1
        ~specs:specs1
        ~use_fun_input_regs:p.use_fun_input_regs
        ~exp_conds:exp_conds1
        ~stack_range
    in
    let _, env1 = Pre.init_vars (Pre.get_vars env1 main_sub1) env1 in
    env1
  in
  let posts, hyps =
    comparators_of_flags ~orig:(main_sub1, env1) ~modif:(main_sub2, env2) p
  in
  let pre, env1, env2 =
    Comp.compare_subs ~postconds:posts ~hyps:hyps
      ~original:(main_sub1, env1) ~modified:(main_sub2, env2)
  in
  if List.mem p.show "bir" ~equal:String.equal then
    Printf.printf "\nComparing\n\n%s\nand\n\n%s\n%!"
      (Sub.to_string main_sub1) (Sub.to_string main_sub2);
  { pre = pre; orig = env1, main_sub1; modif = env2, main_sub2 }

let check_pre (p : Params.t) (ctx : Z3.context) (cp : combined_pre)
  : (unit, error) result =
  let solver = Z3.Solver.mk_solver ctx None in
  if (List.mem p.debug "constraint-stats" ~equal:(String.equal)) then
    Constr.print_stats cp.pre;
  let debug_eval =
    (List.mem p.debug "eval-constraint-stats" ~equal:(String.equal)) in
  let result = Pre.check ~print_constr:p.show ~debug:debug_eval
      solver ctx cp.pre in
  if (List.mem p.debug "z3-solver-stats" ~equal:(String.equal)) then
    Printf.printf "Showing solver statistics : \n %s \n %!" (
      Z3.Statistics.to_string (Z3.Solver.get_statistics solver));
  let env2, _ = cp.modif in
  Utils.output_to_gdb ~filename:p.gdb_output ~func:p.func solver result env2;
  Utils.output_to_bildb ~filename:p.bildb_output solver result env2;
  Output.print_result solver result cp.pre ~orig:cp.orig
    ~modif:cp.modif ~show:p.show;
  Ok ()

(* Entrypoint for the WP analysis. *)
let run (p : Params.t) (files : string list) (bap_ctx : ctxt)
  : (unit, error) result =
  if (List.mem p.debug "z3-verbose"  ~equal:(String.equal)) then
    Z3.set_global_param "verbose" "10";
  let z3_ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  Utils.update_default_num_unroll p.num_unroll;
  (* Determine whether to perform a single or comparative analysis. *)
  match files with
  | [file] ->
    single bap_ctx z3_ctx var_gen p file
    |> check_pre p z3_ctx
  | [file1; file2] ->
    comparative bap_ctx z3_ctx var_gen p file1 file2
    |> check_pre p z3_ctx
  | _ ->
    let err =
      Printf.sprintf "WP can only analyze one binary for a single analysis or \
                     two binaries for a comparative analysis. Number of \
                     binaries provided: %d.%!" (List.length files) in
    Error (Unsupported_file_count err)
