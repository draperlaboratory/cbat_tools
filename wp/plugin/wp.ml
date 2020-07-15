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
    compare_post_reg_values : string list;
    gdb_filename : string option;
    bildb_output : string option;
    use_fun_input_regs : bool;
    mem_offset : bool;
    check_null_deref : bool;
    debug : string list;
    trip_asserts : bool;
    stack_base : int option;
    stack_size : int option;
    show : string list
  }

type combined_pre =
  {
    pre : Constr.t;
    orig : Env.t * Sub.t;
    modif : Env.t * Sub.t
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
    let () =
      if Seq.length_is_bounded_by ~min:1 filter_subs then
        info "Inlining functions: %s\n" (filter_subs |> Seq.to_list |> List.to_string ~f:Sub.name)
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

let fun_specs (f : flags) (to_inline : Sub.t Seq.t)
  : (Sub.t -> Arch.t -> Env.fun_spec option) list =
  let default =
    [ Pre.spec_verifier_assume;
      Pre.spec_verifier_nondet;
      Pre.spec_afl_maybe_log;
      Pre.spec_inline to_inline;
      Pre.spec_empty;
      Pre.spec_arg_terms;
      Pre.spec_chaos_caller_saved;
      Pre.spec_rax_out
    ] in
  if f.trip_asserts then
    Pre.spec_verifier_error :: default
  else
    default

let set_stack (f : flags) : Env.mem_range =
  let update_base stack_base range =
    match stack_base with
    | None -> range
    | Some base -> Env.update_stack_base range base in
  let update_size stack_size range =
    match stack_size with
    | None -> range
    | Some size -> Env.update_stack_size range size in
  Pre.default_stack_range
  |> update_base f.stack_base
  |> update_size f.stack_size

let analyze_proj (ctx : Z3.context) (var_gen : Env.var_gen) (proj : project)
    (flags : flags) : combined_pre =
  let arch = Project.arch proj in
  let subs = proj |> Project.program |> Term.enum sub_t in
  let main_sub = find_func_err subs flags.func in
  let to_inline = match_inline flags.inline subs in
  let specs = fun_specs flags to_inline in
  let exp_conds = exp_conds_mod flags in
  let stack_range = set_stack flags in
  let env = Pre.mk_env ctx var_gen ~subs ~arch ~specs
      ~use_fun_input_regs:flags.use_fun_input_regs ~exp_conds ~stack_range in
  (* call visit sub with a dummy postcondition to fill the
     environment with variables *)
  let true_constr = Env.trivial_constr env in
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
  if List.mem flags.show "bir" ~equal:String.equal then
    Printf.printf "\nSub:\n%s\n%!" (Sub.to_string main_sub);
  { pre = pre; orig = env, main_sub; modif = env, main_sub }

let check_calls (flag : bool) : (Comp.comparator * Comp.comparator) option =
  if flag then
    Some Comp.compare_subs_fun
  else
    None

let post_reg_values
    (flag : string list)
    ~orig:(sub1, env1 : Sub.t * Env.t)
    ~modif:(sub2, env2 : Sub.t * Env.t)
  : (Comp.comparator * Comp.comparator) option =
  if List.is_empty flag then
    None
  else begin
    let all_regs = Var.Set.union
        (Pre.get_vars env1 sub1) (Pre.get_vars env2 sub2) in
    let post_regs = Var.Set.union
        (Pre.set_of_reg_names env1 sub1 flag)
        (Pre.set_of_reg_names env2 sub2 flag) in
    debug "Pre register vals: %s%!" (varset_to_string all_regs);
    debug "Post register vals: %s%!" (varset_to_string post_regs);
    Some (Comp.compare_subs_eq ~pre_regs:all_regs ~post_regs:post_regs)
  end

let smtlib
    ~post_cond:(post_cond : string)
    ~pre_cond:(pre_cond : string)
  : (Comp.comparator * Comp.comparator) option =
  if String.is_empty post_cond && String.is_empty pre_cond then
    None
  else
    Some (Comp.compare_subs_smtlib ~smtlib_post:post_cond ~smtlib_hyp:pre_cond)

let sp (arch : Arch.t) : (Comp.comparator * Comp.comparator) option =
  match arch with
  | `x86_64 -> Some Comp.compare_subs_sp
  | _ ->
    error "CBAT can only generate hypotheses about the stack pointer and \
           memory for the x86_64 architecture.\n%!";
    None

(* Returns a list of postconditions and a list of hypotheses based on the flags
   set from the command line. *)
let comparators_of_flags
    ~orig:(sub1, env1 : Sub.t * Env.t)
    ~modif:(sub2, env2 : Sub.t * Env.t)
    (flags : flags)
  : Comp.comparator list * Comp.comparator list =
  let arch = Env.get_arch env1 in
  let comps =
    [ check_calls flags.check_calls;
      post_reg_values flags.compare_post_reg_values
        ~orig:(sub1, env1) ~modif:(sub2, env2);
      smtlib ~post_cond:flags.post_cond ~pre_cond:flags.pre_cond;
      sp arch ]
    |> List.filter_opt
  in
  let comps =
    if List.is_empty comps then
      [Comp.compare_subs_empty_post]
    else
      comps
  in
  List.unzip comps

let compare_projs (ctx : Z3.context) (var_gen : Env.var_gen) (proj : project)
    (flags : flags) : combined_pre =
  let prog1 = Program.Io.read flags.file1 in
  let prog2 = Program.Io.read flags.file2 in
  (* Currently using the dummy binary's project to determine the architecture
     until we discover a better way of determining the architecture from a program. *)
  let arch = Project.arch proj in
  let subs1 = Term.enum sub_t prog1 in
  let subs2 = Term.enum sub_t prog2 in
  let main_sub1 = find_func_err subs1 flags.func in
  let main_sub2 = find_func_err subs2 flags.func in
  let stack_range = set_stack flags in
  let env2 =
    let to_inline2 = match_inline flags.inline subs2 in
    let specs2 = fun_specs flags to_inline2 in
    let exp_conds2 = exp_conds_mod flags in
    let env2 = Pre.mk_env ctx var_gen ~subs:subs2 ~arch:arch ~specs:specs2
        ~use_fun_input_regs:flags.use_fun_input_regs ~exp_conds:exp_conds2 ~stack_range in
    let env2 = Env.set_freshen env2 true in
    let _, env2 = Pre.init_vars (Pre.get_vars env2 main_sub2) env2 in
    env2
  in
  let env1 =
    let to_inline1 = match_inline flags.inline subs1 in
    let specs1 = fun_specs flags to_inline1 in
    let exp_conds1 = exp_conds_orig flags env2 in
    let env1 = Pre.mk_env ctx var_gen ~subs:subs1 ~arch:arch ~specs:specs1
        ~use_fun_input_regs:flags.use_fun_input_regs ~exp_conds:exp_conds1 ~stack_range in
    let _, env1 = Pre.init_vars (Pre.get_vars env1 main_sub1) env1 in
    env1
  in
  let posts, hyps =
    comparators_of_flags ~orig:(main_sub1, env1) ~modif:(main_sub2, env2) flags
  in
  let pre, env1, env2 =
    Comp.compare_subs ~postconds:posts ~hyps:hyps
      ~original:(main_sub1, env1) ~modified:(main_sub2, env2)
  in
  if List.mem flags.show "bir" ~equal:String.equal then
    Printf.printf "\nComparing\n\n%s\nand\n\n%s\n%!"
      (Sub.to_string main_sub1) (Sub.to_string main_sub2);
  { pre = pre; orig = env1, main_sub1; modif = env2, main_sub2 }

let should_compare (f : flags) : bool =
  f.compare || ((not @@ String.is_empty f.file1) && (not @@ String.is_empty f.file2))

let check_show (show : string list) : unit =
  let options = ["bir"; "refuted-goals"; "paths"; "precond-internal"; "precond-smtlib"] in
  match List.find show ~f:(fun s -> not @@ List.mem options s ~equal:String.equal) with
  | Some s ->
    Printf.printf "'%s' is not a valid option for --wp-show. Available options \
                   are: %s\n%!" s (List.to_string options ~f:String.to_string);
    exit 1
  | None -> ()

let main (flags : flags) (proj : project) : unit =
  if (List.mem flags.debug "z3-verbose"  ~equal:(String.equal)) then
    Z3.set_global_param "verbose" "10";
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let solver = Z3.Solver.mk_solver ctx None in
  update_default_num_unroll flags.num_unroll;
  let combined_pre =
    if should_compare flags then
      compare_projs ctx var_gen proj flags
    else
      analyze_proj ctx var_gen proj flags
  in
  if (List.mem flags.debug "constraint-stats" ~equal:(String.equal)) then
    Constr.print_stats (combined_pre.pre);
  let debug_eval =
    (List.mem flags.debug "eval-constraint-stats" ~equal:(String.equal)) in
  let result = Pre.check ~print_constr:flags.show ~debug:debug_eval
      solver ctx combined_pre.pre in
  if (List.mem flags.debug "z3-solver-stats" ~equal:(String.equal)) then
    Printf.printf "Showing solver statistics : \n %s \n %!" (
      Z3.Statistics.to_string (Z3.Solver.get_statistics solver));
  let env2, _ = combined_pre.modif in
  let () = match flags.gdb_filename with
    | None -> ()
    | Some f -> Output.output_gdb solver result env2 ~func:flags.func ~filename:f in
  let () = match flags.bildb_output with
    | None -> ()
    | Some f -> Output.output_bildb solver result env2 f in
  Output.print_result solver result combined_pre.pre ~orig:combined_pre.orig
    ~modif:combined_pre.modif ~show:flags.show


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
            body. This flag is only used in comparative analysis."

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

  let compare_post_reg_values = param (list string) "compare-post-reg-values"
      ~default:[]
      ~doc:"This flag is used for a comparison analysis. If set, WP will \
            compare the values stored in the specified registers at the end of \
            the analyzed function's execution. For example, \
            --wp-compare-post-reg-values=RAX,RDI compares the values of RAX \
            and RDI at the end of execution. If unsure about which registers \
            to compare, x86_64 architectures place their output in RAX, and \
            ARM architectures place their output in R0."

  let gdb_filename = param (some string) "gdb-filename" ~default:None
      ~doc:"Output gdb script file for counterexample. This script file sets a \
            breakpoint at the the start of the function being analyzed and sets \
            the registers and memory to the values specified in the countermodel."

  let bildb_output = param (some string) "bildb-output" ~default:None
      ~doc:"In the case CBAT determins input registers that result in a refuted \
            goal, this flag outputs a BilDB YAML file to the filename specified. \
            This file sets the registers and memory to the values specified in the \
            countermodel found during WP analysis, allowing BilDB to follow the \
            same execution trace."

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
            dereferencing a NULL value. In the case of a comparative analysis, \
            asserts that if a memory read or write in the original binary does \
            not dereference a NULL, then that same read or write in the modified \
            binary also does not dereference a NULL. Defaults to false."

  let debug = param (list string) "debug" ~default:[]
      ~as_flag:["z3-solver-stats"; "z3-verbose"; "constraint-stats"; "eval-constraint-stats"]
      ~doc:"If set, debug will print the various debugging statistics, including \
            information and statistics for Z3's solver, Z3's verbosity-level, \
            constr.t, and expression-lists when calling eval. These can also be \
            called with the key-words: z3-solver-stats, z3-verbose, constraint-stats \
            and eval-constraint-stats respectively. If the flag is not called, it \
            defaults to printing none of them."

  let show = param (list string) "show" ~default:[]
      ~doc:"A list of details to print out from the analysis. Multiple options \
            as a list can be passed into the flag to print out multiple details. \
            For example: `--wp-show=bir,refuted-goals'. \
            The options are:\n \
            `bir': The code of the binary/binaries in BAP Immediate \
            Representation.\n \
            `refuted-goals': In the case the analysis results in SAT, a list \
            of goals refuted in the model that contains their tagged names, the \
            concrete values of the goals, and the Z3 representation of the goal.\n \
            `paths': The execution path of the binary that results in a refuted \
            goal. The path contains information about the jumps taken, their \
            addresses, and the values of the registers at each jump. This option \
            automatically prints out the refuted-goals.\n \
            `precond-internal': The precondition printed out in WP's internal \
            format for the Constr.t type.\n \
           `precond-smtlib': The precondition printed out in Z3's SMT-LIB2 \
            format."

  let trip_asserts = param bool "trip-asserts" ~as_flag:true ~default:false
      ~doc:"If set, WP will look for inputs to the subroutine that would cause \
            an __assert_fail or __VERIFIER_error to be reached."

  let stack_base = param (some int) "stack-base" ~default:None
      ~doc:"The default address of the stack base. WP assumes the stack base \
            is the highest address and the stack grows downward. By default, \
            set to 0x40000000."

  let stack_size = param (some int) "stack-size" ~default:None
      ~doc:"The default size of the stack in bytes. By default, set to \
            0x800000 which is 8Mbs."

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
          compare_post_reg_values = !!compare_post_reg_values;
          gdb_filename = !!gdb_filename;
          bildb_output = !!bildb_output;
          use_fun_input_regs = !!use_fun_input_regs;
          mem_offset = !!mem_offset;
          check_null_deref = !!check_null_deref;
          debug = !!debug;
          trip_asserts = !!trip_asserts;
          stack_base = !!stack_base;
          stack_size = !!stack_size;
          show = !!show
        }
      in
      check_show flags.show;
      Project.register_pass' @@
      main flags
    )

  let () = manpage [
      `S "DESCRIPTION";
      `P "Computes the weakest precondition of a subroutine given a postcondition."
    ]
end
