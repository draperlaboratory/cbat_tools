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
open Bap_wp
include Self()

module Comp = Compare
module Pre = Precondition
module Env = Environment
module Constr = Constraint

type flags =
  {
    compare: bool;
    file1 : string;
    file2 : string;
    func : string;
    check_calls : bool;
    inline : string option;
    pre_cond : string;
    post_cond : string;
    num_unroll : int option;
    output_vars : string list;
    gdb_filename : string option;
    print_path : bool;
    use_fun_input_regs : bool;
    mem_offset : bool;
    check_null_deref : bool
  }

let missing_func_msg (func : string) : string =
  Format.sprintf "Missing function: %s is not in binary." func

let diff_arch_msg (arch1 : Arch.t) (arch2 : Arch.t) : string =
  Format.sprintf "Binaries are of two different architectures: %s vs %s"
    (Arch.to_string arch1) (Arch.to_string arch2)

let find_func_err (subs : Sub.t Seq.t) (func : string) : Sub.t =
  match Seq.find ~f:(fun s -> String.equal (Sub.name s) func) subs with
  | None -> failwith (missing_func_msg func)
  | Some f -> f

(* Not efficient, but easier to read *)
let find_func_in_one_of (f : string) ~to_find:(to_find : Sub.t Seq.t)
    ~to_check:(to_check : Sub.t Seq.t) : Sub.t list =
  match Seq.find ~f:(fun s -> String.equal (Sub.name s) f) to_find with
  | None -> if Option.is_some (Seq.find ~f:(fun s -> String.equal (Sub.name s) f) to_check)
    then []
    else failwith (missing_func_msg f)
  | Some f -> [f]

let update_default_num_unroll (num_unroll : int option) : unit =
  match num_unroll with
  | Some n -> Pre.num_unroll := n
  | None -> ()

let match_inline (to_inline : string option) (subs : (Sub.t Seq.t)) : Sub.t Seq.t =
  match to_inline with
  | None -> Seq.empty
  | Some to_inline -> let inline_pat = Re.Posix.re to_inline |> Re.Posix.compile in
    let filter_subs = Seq.filter ~f:(fun s -> Re.execp inline_pat (Sub.name s)) subs in
    let _ = if Seq.length_is_bounded_by ~min:1 filter_subs then
        info "Inlining functions: %s\n"  (filter_subs |> Seq.to_list |> List.to_string ~f:(fun sub -> (Sub.name sub)))
      else
        warning "No matches on inlining\n"
    in
    filter_subs

let varset_to_string (vs : Var.Set.t) : string =
  vs
  |> Var.Set.to_sequence
  |> Seq.to_list
  |> List.to_string ~f:Var.to_string

(* If an offset is specified, generates a function of the address of a memory read in
   the original binary to the address plus an offset in the modified binary. *)
let get_mem_offsets (ctx : Z3.context) (flags : flags)
  : Constr.z3_expr -> Constr.z3_expr =
  if flags.mem_offset then
    let get_symbols file =
      (* Chopping off the bpj to get the original binaries rather than the saved
         project files. *)
      file
      |> String.chop_suffix_exn ~suffix:".bpj"
      |> Symbol.get_symbols
    in
    let syms_orig = get_symbols flags.file1 in
    let syms_mod = get_symbols flags.file2 in
    Symbol.offset_constraint ~orig:syms_orig ~modif:syms_mod ctx
  else
    fun addr -> addr

(* Generate the exp_conds for the original binary based on the flags passed in
   from the CLI. Generating the memory offsets requires the environment of
   the modified binary. *)
let exp_conds_orig (flags : flags) (env_mod : Env.t) : Env.exp_cond list =
  let ctx = Env.get_context env_mod in
  let offsets =
    get_mem_offsets ctx flags
    |> Pre.mem_read_offsets env_mod
  in
  if flags.check_null_deref then
    [Pre.non_null_load_assert; Pre.non_null_store_assert; offsets]
  else
    [offsets]

(* Generate the exp_conds for the modified binary based on the flags passed in
   from the CLI. *)
let exp_conds_mod (flags : flags) : Env.exp_cond list =
  if flags.check_null_deref then
    [Pre.non_null_load_vc; Pre.non_null_store_vc]
  else
    []

let analyze_proj (ctx : Z3.context) (var_gen : Env.var_gen) (proj : project)
    (flags : flags) : Constr.t * Env.t * Env.t =
  let arch = Project.arch proj in
  let subs = proj |> Project.program |> Term.enum sub_t in
  let main_sub = find_func_err subs flags.func in
  let to_inline = match_inline flags.inline subs in
  let exp_conds = exp_conds_mod flags in
  let env = Pre.mk_env ctx var_gen ~subs ~arch ~to_inline
      ~use_fun_input_regs:flags.use_fun_input_regs ~exp_conds in
  (* call visit sub with a dummy postcondition to fill the
     environment with variables *)
  let true_constr = Pre.Bool.mk_true ctx |> Constr.mk_goal "true" |> Constr.mk_constr in
  let _, env = Pre.visit_sub env true_constr main_sub in
  (* Remove the constants generated and stored in the environment because they aren't
     going to be used in the wp analysis. *)
  let env = Env.clear_consts env in
  let hyps, env = Pre.init_vars (Pre.get_vars env main_sub) env in
  let hyps = (Pre.set_sp_range env) :: hyps in
  let post =
    if String.is_empty flags.post_cond then
      true_constr
    else
      Z3_utils.mk_smtlib2_single env flags.post_cond
  in
  let pre, env = Pre.visit_sub env post main_sub in
  let pre = Constr.mk_clause [Z3_utils.mk_smtlib2_single env flags.pre_cond] [pre] in
  let pre = Constr.mk_clause hyps [pre] in
  Format.printf "\nSub:\n%s\nPre:\n%a\n%!"
    (Sub.to_string main_sub) Constr.pp_constr pre;
  (pre, env, env)

let compare_projs (ctx : Z3.context) (var_gen : Env.var_gen) (proj : project)
    (flags : flags) : Constr.t * Env.t * Env.t =
  let prog1 = Program.Io.read flags.file1 in
  let prog2 = Program.Io.read flags.file2 in
  (* Currently using the dummy binary's project to determine the architecture
     until we discover a better way of determining the architecture from a program. *)
  let arch = Project.arch proj in
  let subs1 = Term.enum sub_t prog1 in
  let subs2 = Term.enum sub_t prog2 in
  let main_sub1 = find_func_err subs1 flags.func in
  let main_sub2 = find_func_err subs2 flags.func in
  let env2 =
    let to_inline2 = match_inline flags.inline subs2 in
    let exp_conds2 = exp_conds_mod flags in
    let env2 = Pre.mk_env ctx var_gen ~subs:subs2 ~arch:arch ~to_inline:to_inline2
        ~use_fun_input_regs:flags.use_fun_input_regs ~exp_conds:exp_conds2 in
    let env2 = Env.set_freshen env2 true in
    let _, env2 = Pre.init_vars (Pre.get_vars env2 main_sub2) env2 in
    env2
  in
  let env1 =
    let to_inline1 = match_inline flags.inline subs1 in
    let exp_conds1 = exp_conds_orig flags env2 in
    let env1 = Pre.mk_env ctx var_gen ~subs:subs1 ~arch:arch ~to_inline:to_inline1
        ~use_fun_input_regs:flags.use_fun_input_regs ~exp_conds:exp_conds1 in
    let _, env1 = Pre.init_vars (Pre.get_vars env1 main_sub1) env1 in
    env1
  in
  let pre, env1, env2 =
    if flags.check_calls then
      Comp.compare_subs_fun ~original:(main_sub1,env1) ~modified:(main_sub2,env2)
    else
      begin
        let output_vars = Var.Set.union
            (Pre.get_output_vars env1 main_sub1 flags.output_vars)
            (Pre.get_output_vars env2 main_sub2 flags.output_vars) in
        let input_vars = Var.Set.union
            (Pre.get_vars env1 main_sub1) (Pre.get_vars env2 main_sub2) in
        debug "Input: %s%!" (varset_to_string input_vars);
        debug "Output: %s%!" (varset_to_string output_vars);
        Comp.compare_subs_eq ~input:input_vars ~output:output_vars
          ~original:(main_sub1,env1) ~modified:(main_sub2,env2)
          ~smtlib_post:flags.post_cond ~smtlib_hyp:flags.pre_cond
      end
  in
  Format.printf "\nComparing\n\n%s\nand\n\n%s\n%!"
    (Sub.to_string main_sub1) (Sub.to_string main_sub2);
  (pre, env1, env2)

let should_compare (f : flags) : bool =
  f.compare || ((not @@ String.is_empty f.file1) && (not @@ String.is_empty f.file2))

let main (flags : flags) (proj : project) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let solver = Z3.Solver.mk_simple_solver ctx in
  update_default_num_unroll flags.num_unroll;
  let pre, env1, env2 =
    if should_compare flags then
      compare_projs ctx var_gen proj flags
    else
      analyze_proj ctx var_gen proj flags
  in
  let result = Pre.check solver ctx pre in
  let () = match flags.gdb_filename with
    | None -> ()
    | Some f ->
      Printf.printf "Dumping gdb script to file: %s\n" f;
      Output.output_gdb solver result env2 ~func:flags.func ~filename:f in
  Output.print_result solver result pre ~print_path:flags.print_path
    ~orig:env1 ~modif:env2


module Cmdline = struct
  open Config

  let compare = param bool "compare" ~as_flag:true ~default:false
      ~doc:"Determines whether to analyze a single function or compare the same \
            function across two binaries. If enabled, project files must be specified \
            with the `file1' and `file2' options."

  let file1 = param string "file1" ~default:""
      ~doc:"Project file location of the first binary for comparative analysis, \
            which can be generated via the save-project plugin. If both `file1' and \
            `file2' are specified, wp will automatically run the comparative analysis."

  let file2 = param string "file2" ~default:""
      ~doc:"Project file location of the second binary for comparative analysis, \
            which can be generated via the save-project plugin. If both `file1' and \
            `file2' are specified, wp will automatically run the comparative analysis."

  let func = param string "function" ~synonyms:["func"] ~default:"main"
      ~doc:"Function to run the wp analysis on. `main' by default. If the function \
            cannot be found in the binary or both binaries in the comparison \
            case, wp analysis should fail."

  let check_calls = param bool "check-calls" ~as_flag:true ~default:false
      ~doc:"If set, compares which subroutines are invoked in the body of the \
            function. Otherwise, compares the return values computed in the function \
            body."

  let inline = param (some string) "inline" ~default:None
      ~doc:"Function calls to inline as specified by a POSIX regular expression. \
            If not inlined, function summaries are used at function call time. \
            If you want to inline everything, set to .*  \
            foo|bar will inline the functions foo and bar."

  let pre_cond = param string "precond" ~default:""
      ~doc:"Pre condition in SMT-LIB format used when analyzing a single binary. \
            If no pre condition is specified, a trivial pre condition (`true') \
            will be used."

  let post_cond = param string "postcond" ~default:""
      ~doc:"Post condition in SMT-LIB format used when analyzing a single binary. \
            If no post condition is specified, a trivial post condition (`true') \
            will be used."

  let num_unroll = param (some int) "num-unroll" ~default:None
      ~doc:"Amount of times to unroll each loop. By default, wp will unroll each \
            loop 5 times."

  let output_vars = param (list string) "output-vars" ~default:["RAX"; "EAX"]
      ~doc:"List of output variables to compare separated by `,' given the same \
            input variables in the case of a comparative analysis. Defaults to `RAX,EAX' \
            which are the 64- and 32-bit output registers for x86."

  let gdb_filename = param (some string) "gdb-filename" ~default:None
      ~doc:"Output gdb script file for counterexample. This script file sets a \
            breakpoint at the the start of the function being analyzed and sets \
            the registers and memory to the values specified in the countermodel."

  let print_path = param bool "print-path" ~as_flag:true ~default:false
      ~doc:"If set, prints out the path to a refuted goal and the register values \
            at each jump in the path. The path contains information about whether \
            a jump has been taken and the address of the jump if found."

  let use_fun_input_regs = param bool "use-fun-input-regs" ~as_flag:true  ~default:true
      ~doc:"If set, at a function call site, uses all possible input registers \
            as arguments to a function symbol generated for an output register \
            that represents the result of the function call. If set to false, no \
            registers will be used. Defaults to true."

  let mem_offset = param bool "mem-offset" ~as_flag:true ~default:false
      ~doc:"If set, at every memory read, adds an assumption to the precondition that \
            memory of the modified binary is the same as the original binary at an \
            offset calculated by aligning the data and bss sections of the binary. \
            Defaults to false."

  let check_null_deref = param bool "check-null-deref" ~as_flag:true ~default:false
      ~doc:"If set, the WP analysis will check for inputs that would result in \
            dereferencing a NULL value. Defaults to false."

  let () = when_ready (fun {get=(!!)} ->
      let flags =
        {
          compare = !!compare;
          file1 = !!file1;
          file2 = !!file2;
          func = !!func;
          check_calls = !!check_calls;
          inline = !!inline;
          pre_cond = !!pre_cond;
          post_cond = !!post_cond;
          num_unroll = !!num_unroll;
          output_vars = !!output_vars;
          gdb_filename = !!gdb_filename;
          print_path = !!print_path;
          use_fun_input_regs = !!use_fun_input_regs;
          mem_offset = !!mem_offset;
          check_null_deref = !!check_null_deref
        }
      in
      Project.register_pass' @@
      main flags
    )

  let () = manpage [
      `S "DESCRIPTION";
      `P "Computes the weakest precondition of a subroutine given a postcondition."
    ]
end
