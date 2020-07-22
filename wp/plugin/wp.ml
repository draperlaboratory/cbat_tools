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
open Bap_knowledge
open Bap.Std
open Regular.Std
open Bap_wp
include Self()

module Cmd = Bap_main.Extension.Command
module Conf = Bap_main.Extension.Configuration
module Typ = Bap_main.Extension.Type

module Comp = Compare
module Pre = Precondition
module Env = Environment
module Constr = Constraint

module Digests = struct

  (* Returns a function that makes digests. *)
  let get_generator ctx filepath loader =
    let inputs = [Conf.digest ctx; Caml.Digest.file filepath; loader] in
    let subject = String.concat inputs in
    fun ~namespace ->
      let d = Data.Cache.Digest.create ~namespace in
      Data.Cache.Digest.add d "%s" subject

  (* Creates a digest for the knowledge cache. *)
  let knowledge mk_digest = mk_digest ~namespace:"knowledge"

  (* Creates a digest for the project state cache. *)
  let project mk_digest = mk_digest ~namespace:"project"

end


module Knowledge_cache = struct

  (* Creates the knowledge cache. *)
  let knowledge_cache () =
    let reader = Data.Read.create ~of_bigstring:Knowledge.of_bigstring () in
    let writer = Data.Write.create ~to_bigstring:Knowledge.to_bigstring () in
    Data.Cache.Service.request reader writer

  (* Loads knowledge (if any) from the knowledge cache. *)
  let load digest =
    let cache = knowledge_cache () in
    match Data.Cache.load cache digest with
    | None -> ()
    | Some state -> Toplevel.set state

  (* Saves knowledge in the knowledge cache. *)
  let save digest =
    let cache = knowledge_cache () in
    Toplevel.current ()
    |> Data.Cache.save cache digest

end


module Project_cache = struct

  (* Creates a project state cache. *)
  let project_cache () =
    let module State = struct
      type t = Project.state [@@deriving bin_io]
    end in
    let of_bigstring = Binable.of_bigstring (module State) in
    let to_bigstring = Binable.to_bigstring (module State) in
    let reader = Data.Read.create ~of_bigstring () in
    let writer = Data.Write.create ~to_bigstring () in
    Data.Cache.Service.request reader writer

  (* Loads project state (if any) from the cache. *)
  let load digest : Project.state option =
    let cache = project_cache () in
    Data.Cache.load cache digest

  (* Saves project state in the cache. *)
  let save digest state =
    let cache = project_cache () in
    Data.Cache.save cache digest state

end


module Utils = struct

  let loader = "llvm"

  let api = "api"

  (* Runs the API pass on the project to determine argument terms for each
     subroutine. *)
  let api_pass (proj : Project.t) : Project.t =
    match Project.find_pass api with
    | Some pass -> Project.Pass.run_exn pass proj
    | None -> failwith "API pass not found! Check if bap-api is installed.%!"

  (* Loads a BAP project from a binary file. *)
  let load_proj (package : string) (loader : string) (filename : string)
    : Project.t =
    let input = Project.Input.file ~loader ~filename in
    match Project.create ~package input with
    | Ok proj -> api_pass proj
    | Error e ->
      let msg = Error.to_string_hum e in
      failwith (Printf.sprintf "Error loading project: %s\n%!" msg)

  (* Finds a function in the binary. *)
  let find_func_err (subs : Sub.t Seq.t) (func : string) : Sub.t =
    match Seq.find ~f:(fun s -> String.equal (Sub.name s) func) subs with
    | None ->
      let msg = Printf.sprintf "Missing function: %s is not in binary.%!" func in
      failwith msg
    | Some f -> f

  (* Finds a sequence of subroutines to inline based on the regex from the
     user. *)
  let match_inline (to_inline : string option) (subs : (Sub.t Seq.t))
    : Sub.t Seq.t =
    match to_inline with
    | None -> Seq.empty
    | Some to_inline ->
      let inline_pat = Re.Posix.re to_inline |> Re.Posix.compile in
      let filter_subs =
        Seq.filter ~f:(fun s -> Re.execp inline_pat (Sub.name s)) subs
      in
      let () =
        if Seq.is_empty filter_subs then
          warning "No matches on inlining. Regex: %s\n%!%!" to_inline
        else
          info "Inlining functions: %s%!\n"
            (filter_subs |> Seq.to_list |> List.to_string ~f:Sub.name)
      in
      filter_subs

  (* Converts a set of variables to a string for printing debug logs. *)
  let varset_to_string (vs : Var.Set.t) : string =
    vs
    |> Var.Set.to_sequence
    |> Seq.to_list
    |> List.to_string ~f:Var.to_string

  (* Updates the number of times to unroll a loop based on the user's input. *)
  let update_default_num_unroll (num_unroll : int option) : unit =
    match num_unroll with
    | Some n -> Pre.num_unroll := n
    | None -> ()

  (* Updates the stack's base/size based on the user's input. *)
  let update_stack ~base:(base : int option) ~size:(size : int option)
    : Env.mem_range =
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

  (* Checks the user's input for outputting a gdb script. *)
  let output_to_gdb filename func solver status env : unit =
    match filename with
    | None -> ()
    | Some name -> Output.output_gdb ~filename:name ~func solver status env

  (* Checks the user's input for outputting a bildb script. *)
  let output_to_bildb filename solver result env : unit =
   match filename with
    | None -> ()
    | Some name -> Output.output_bildb solver result env name

end


module Analysis = struct

  type flags = {
    func : string;
    precond : string;
    postcond : string;
    trip_asserts : bool;
    check_null_derefs : bool;
    compare_func_calls : bool;
    compare_post_reg_values : string list;
    inline : string option;
    num_unroll : int option;
    gdb_output : string option;
    bildb_output : string option;
    use_fun_input_regs : bool;
    mem_offset : bool;
    debug : string list;
    stack_base : int option;
    stack_size : int option;
    files : string list;
    show : string list
  }

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
  let get_mem_offsets (ctx : Z3.context) (f : flags) (file1 : string)
      (file2 : string) : Constr.z3_expr -> Constr.z3_expr =
    if f.mem_offset then
      let syms_orig = Symbol.get_symbols file1 in
      let syms_mod = Symbol.get_symbols file2 in
      Symbol.offset_constraint ~orig:syms_orig ~modif:syms_mod ctx
    else
      fun addr -> addr

  (* Generate the exp_conds for the original binary based on the flags passed in
     from the CLI. Generating the memory offsets requires the environment of
     the modified binary. *)
  let exp_conds_orig (f : flags) (env_mod : Env.t) (file1 : string)
      (file2 : string) : Env.exp_cond list =
    let ctx = Env.get_context env_mod in
    let offsets =
      get_mem_offsets ctx f file1 file2
      |> Pre.mem_read_offsets env_mod
    in
    if f.check_null_derefs then
      [Pre.non_null_load_assert; Pre.non_null_store_assert; offsets]
    else
      [offsets]

  (* Generate the exp_conds for the modified binary based on the flags passed in
     from the CLI. *)
  let exp_conds_mod (f : flags) : Env.exp_cond list =
    if f.check_null_derefs then
      [Pre.non_null_load_vc; Pre.non_null_store_vc]
    else
      []

  (* Determine which function specs to use in WP. *)
  let fun_specs (f : flags) (to_inline : Sub.t Seq.t)
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
    if f.trip_asserts then
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

  (* Returns a list of postconditions and a list of hypotheses based on the
     flags set from the command line. *)
  let comparators_of_flags
      ~orig:(sub1, env1 : Sub.t * Env.t)
      ~modif:(sub2, env2 : Sub.t * Env.t)
      (f : flags)
    : Comp.comparator list * Comp.comparator list =
    let arch = Env.get_arch env1 in
    let comps = [
      func_calls f.compare_func_calls;
      post_reg_values f.compare_post_reg_values
        ~orig:(sub1, env1) ~modif:(sub2, env2);
      smtlib ~precond:f.precond ~postcond:f.postcond;
      sp arch
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
  let single (ctx : Z3.context) (var_gen : Env.var_gen) (f : flags)
      (file : string) : combined_pre =
    let proj = Utils.load_proj "wp" Utils.loader file in
    let arch = Project.arch proj in
    let subs = proj |> Project.program |> Term.enum sub_t in
    let main_sub = Utils.find_func_err subs f.func in
    let to_inline = Utils.match_inline f.inline subs in
    let specs = fun_specs f to_inline in
    let exp_conds = exp_conds_mod f in
    let stack_range = Utils.update_stack ~base:f.stack_base ~size:f.stack_size in
    let env = Pre.mk_env ctx var_gen ~subs ~arch ~specs
        ~use_fun_input_regs:f.use_fun_input_regs ~exp_conds ~stack_range in
    let true_constr = Env.trivial_constr env in
    let hyps, env = Pre.init_vars (Pre.get_vars env main_sub) env in
    let hyps = (Pre.set_sp_range env) :: hyps in
    let post =
      if String.is_empty f.postcond then
        true_constr
      else
        Z3_utils.mk_smtlib2_single env f.postcond
    in
    let pre, env = Pre.visit_sub env post main_sub in
    let pre = Constr.mk_clause [Z3_utils.mk_smtlib2_single env f.precond] [pre] in
    let pre = Constr.mk_clause hyps [pre] in
    if List.mem f.show "bir" ~equal:String.equal then
      Printf.printf "\nSub:\n%s\n%!" (Sub.to_string main_sub);
    { pre = pre; orig = env, main_sub; modif = env, main_sub }

  (* Runs a comparative analysis. *)
  let comparative (ctx : Z3.context) (var_gen : Env.var_gen) (f : flags)
      (file1 : string) (file2 : string) : combined_pre =
    let prog1 = Program.Io.read file1 in
    let prog2 = Program.Io.read file2 in
    let subs1 = Term.enum sub_t prog1 in
    let subs2 = Term.enum sub_t prog2 in
    (* Temporarily hardcoding the architecture to x86_64 until we add the
       collator interface. *)
    let arch = `x86_64 in
    let main_sub1 = Utils.find_func_err subs1 f.func in
    let main_sub2 = Utils.find_func_err subs2 f.func in
    let stack_range = Utils.update_stack ~base:f.stack_base ~size:f.stack_size in
    let env2 =
      let to_inline2 = Utils.match_inline f.inline subs2 in
      let specs2 = fun_specs f to_inline2 in
      let exp_conds2 = exp_conds_mod f in
      let env2 = Pre.mk_env ctx var_gen
          ~subs:subs2
          ~arch:arch
          ~specs:specs2
          ~use_fun_input_regs:f.use_fun_input_regs
          ~exp_conds:exp_conds2
          ~stack_range
      in
      let env2 = Env.set_freshen env2 true in
      let _, env2 = Pre.init_vars (Pre.get_vars env2 main_sub2) env2 in
      env2
    in
    let env1 =
      let to_inline1 = Utils.match_inline f.inline subs1 in
      let specs1 = fun_specs f to_inline1 in
      let exp_conds1 = exp_conds_orig f env2 file1 file2 in
      let env1 = Pre.mk_env ctx var_gen
          ~subs:subs1
          ~arch:arch
          ~specs:specs1
          ~use_fun_input_regs:f.use_fun_input_regs
          ~exp_conds:exp_conds1
          ~stack_range
      in
      let _, env1 = Pre.init_vars (Pre.get_vars env1 main_sub1) env1 in
      env1
    in
    let posts, hyps =
      comparators_of_flags ~orig:(main_sub1, env1) ~modif:(main_sub2, env2) f
    in
    let pre, env1, env2 =
      Comp.compare_subs ~postconds:posts ~hyps:hyps
        ~original:(main_sub1, env1) ~modified:(main_sub2, env2)
    in
    if List.mem f.show "bir" ~equal:String.equal then
      Printf.printf "\nComparing\n\n%s\nand\n\n%s\n%!"
        (Sub.to_string main_sub1) (Sub.to_string main_sub2);
    { pre = pre; orig = env1, main_sub1; modif = env2, main_sub2 }

  (* Entrypoint for the WP analysis. *)
  let run (f : flags) : unit =
    if (List.mem f.debug "z3-verbose"  ~equal:(String.equal)) then
      Z3.set_global_param "verbose" "10";
    let ctx = Env.mk_ctx () in
    let var_gen = Env.mk_var_gen () in
    let solver = Z3.Solver.mk_solver ctx None in
    Utils.update_default_num_unroll f.num_unroll;
    let combined_pre =
      (* Determine whether to perform a single or comparative analysis. *)
      match f.files with
      | [file] -> single ctx var_gen f file
      | [file1; file2] -> comparative ctx var_gen f file1 file2
      | _ ->
        Printf.printf "WP can only analyze one binary for a single analysis or \
                       two binaries for a comparative analysis. Number of \
                       binaries provided: %d.%!" (List.length f.files);
        exit 1
    in
    if (List.mem f.debug "constraint-stats" ~equal:(String.equal)) then
      Constr.print_stats combined_pre.pre;
    let debug_eval =
      (List.mem f.debug "eval-constraint-stats" ~equal:(String.equal)) in
    let result = Pre.check ~print_constr:f.show ~debug:debug_eval
        solver ctx combined_pre.pre in
    if (List.mem f.debug "z3-solver-stats" ~equal:(String.equal)) then
      Printf.printf "Showing solver statistics : \n %s \n %!" (
        Z3.Statistics.to_string (Z3.Solver.get_statistics solver));
    let env2, _ = combined_pre.modif in
    Utils.output_to_gdb f.gdb_output f.func solver result env2;
    Utils.output_to_bildb f.bildb_output solver result env2;
    Output.print_result solver result combined_pre.pre ~orig:combined_pre.orig
      ~modif:combined_pre.modif ~show:f.show

end


module Cli = struct

  let name = "wp"

  let doc = "WP is a comparative analysis tool. It can compare two binaries \
             and check thay they behave in similar ways. It can also be used \
             to check a single binary for certain behaviors."

  (* Mandatory arguments. *)

  let files = Cmd.arguments Typ.file
      ~doc:"Path(s) to one or two binaries to analyze. If two binaries are \
            specified, WP will run a comparative analysis."

  let func = Cmd.parameter Typ.(some string) "func"
      ~doc:"Function to run the WP analysis on. If no function is specified or \
            the function cannot be found in the binaries, the analysis will \
            fail."

  (* Arguments that determine which properties CBAT should analyze. *)

  let precond = Cmd.parameter Typ.string "precond"
      ~doc:"A precondition in SMT-LIB format that will be used as a hypothesis \
            to the precondition calculated during WP analysis. If no \
            precondition is specified, a trivial precondition of `true' will \
            be used."

  let postcond = Cmd.parameter Typ.string "postcond"
      ~doc:"A postcondition in SMT-LIB format. This is the postcondition that \
            will be used to calculate the weakest precondition. If no \
            postcondition is specified, a trivial postcondition of `true' will \
            be used."

  let trip_asserts = Cmd.flag "trip-asserts"
      ~doc:"If set, WP will look for inputs to the subroutine that would cause \
            an __assert_fail or __VERIFIER_error to be reached."

  let check_null_derefs = Cmd.flag "check-null-derefs"
      ~doc:"If set, the WP analysis will check for inputs that would result in \
            dereferencing a NULL value. In the case of a comparative analysis, \
            WP will check for inputs that would cause a null dereference in \
            the modified binary, assuminig that the same dereference in the \
            original binary is not a null dereference."

  let compare_func_calls = Cmd.flag "compare-func-calls"
      ~doc:"This flag is used for a comparative analysis, so a \
            /path/to/exe1 and /path/to/exe2 must be provided. If set, WP will \
            check that function calls should not occur in the modified binary \
            if they have not occurred in the original binary."

  let compare_post_reg_values = Cmd.parameter Typ.(list string)
      "compare-post-reg-values"
      ~doc:"This flag is used for a comparatve analysis. If set, WP will \
            compare the values stored in the specified registers at the end of \
            the analyzed function's execution. For example, \
            --compare-post-reg-values=RAX,RDI compares the values of RAX \
            and RDI at the end of execution. If unsure about which registers \
            to compare, x86_64 architectures place their output in RAX, and \
            ARM architectures place their output in R0."

  (* Options. *)

  let inline = Cmd.parameter Typ.(some string) "inline"
      ~doc:"Function calls to inline at a function call site as specified by a \
            POSIX regular expression on the name of the target function. If \
            not inlined, function summaries are used at function call time. To \
            inline everything, set to `.*'. For example, `foo|bar' will inline \
            the functions foo and bar."

  let num_unroll = Cmd.parameter Typ.(some int) "num-unroll"
      ~doc:"Amount of times to unroll each loop. By default, WP will unroll \
            each loop 5 times."

  let gdb_output = Cmd.parameter Typ.(some string) "gdb-output"
      ~doc:"In the case WP determines input registers that result in a refuted \
            goal, this flag outputs a gdb script file to the file specified. \
            This script file sets a breakpoint at the the start of the \
            function being analyzed, and sets the registers and memory to the \
            values specified in the countermodel found during the analysis, \
            allowing GDB to follow the same execution trace."

  let bildb_output = Cmd.parameter Typ.(some string) "bildb-output"
      ~doc:"In the case WP determines input registers that result in a refuted \
            goal, this flag outputs a BilDB YAML file to the filename \
            specified. This file sets the registers and memory to the values \
            specified in the countermodel found during WP analysis, allowing \
            BilDB to follow the same execution trace."

  let use_fun_input_regs = Cmd.flag "use-fun-input-regs"
      ~doc:"If set, at a function call site, uses all possible input registers \
            as arguments to a function symbol generated for an output register \
            that represents the result of the function call. If set to false, \
            no registers will be used. Defaults to true."

  let mem_offset = Cmd.flag "mem-offset"
      ~doc:"If set, maps the symbols in the data and bss sections from their \
            addresses in the original binary to their addresses in the \
            modified binary. This flag is experimental."

  let debug = Cmd.parameter Typ.(list string) "debug"
      ~doc:"If set, debug will print the various debugging statistics, \
            including information and statistics for Z3's solver, Z3's \
            verbosity-level, constr.t, and expression-lists when calling eval. \
            These can also be called with the key-words: z3-solver-stats, \
            z3-verbose, constraint-stats and eval-constraint-stats \
            respectively. If the flag is not called, it defaults to printing \
            none of them."

  let stack_base = Cmd.parameter Typ.(some int) "stack-base"
      ~doc:"The default address of the stack base. WP assumes the stack base \
            is the highest address and the stack grows downward. By default, \
            set to 0x40000000."

  let stack_size = Cmd.parameter Typ.(some int) "stack-size"
      ~doc:"The default size of the stack in bytes. By default, set to \
            0x800000 which is 8Mbs."

  let show = Cmd.parameter Typ.(list string) "show"
      ~doc:"A list of details to print out from the analysis. Multiple options \
            as a list can be passed into the flag to print out multiple \
            details. For example: `--show=bir,refuted-goals'. \
            \
            The options are:\n \
            `bir': The code of the binary/binaries in BAP Immediate \
            Representation.\n \
            \
            `refuted-goals': In the case the analysis results in SAT, a list \
            of goals refuted in the model that contains their tagged names, \
            the concrete values of the goals, and the Z3 representation of the \
            goal.\n \
            \
            `paths': The execution path of the binary that results in a \
            refuted goal. The path contains information about the jumps taken, \
            their addresses, and the values of the registers at each jump. \
            This option automatically prints out the refuted-goals.\n \
            \
            `precond-internal': The precondition printed out in WP's internal \
            format for the Constr.t type.\n \
            \
           `precond-smtlib': The precondition printed out in Z3's SMT-LIB2 \
            format."

  let grammar = Cmd.(
      args
        $ func
        $ precond
        $ postcond
        $ trip_asserts
        $ check_null_derefs
        $ compare_func_calls
        $ compare_post_reg_values
        $ inline
        $ num_unroll
        $ gdb_output
        $ bildb_output
        $ use_fun_input_regs
        $ mem_offset
        $ debug
        $ stack_base
        $ stack_size
        $ show
        $ files)

  (* Ensures the user inputted a function for analysis. *)
  let check_func (func : string option) : string =
    match func with
    | Some f -> f
    | None -> Printf.printf "Function is not provided for analysis.\n%!"; exit 1

  (* Ensures the inputted only supported options for the show flag. *)
  let check_show (show : string list) : unit =
    let opts = [
      "bir";
      "refuted-goals";
      "paths";
      "precond-internal";
      "precond-smtlib"
    ] in
    let find_invalid_option =
      List.find show ~f:(fun s -> not @@ List.mem opts s ~equal:String.equal)
    in
    match find_invalid_option with
    | Some s ->
      Printf.printf "'%s' is not a valid option for --show. Available options \
                     are: %s\n%!" s (List.to_string opts ~f:String.to_string);
      exit 1
    | None -> ()

  (* The callback run when the command is invoked from the command line. *)
  let callback
      (func : string option)
      (precond : string)
      (postcond : string)
      (trip_asserts : bool)
      (check_null_derefs : bool)
      (compare_func_calls : bool)
      (compare_post_reg_values : string list)
      (inline : string option)
      (num_unroll : int option)
      (gdb_output : string option)
      (bildb_output : string option)
      (use_fun_input_regs : bool)
      (mem_offset : bool)
      (debug : string list)
      (stack_base : int option)
      (stack_size : int option)
      (show : string list)
      (files : string list)
      (_ : ctxt) =
    let func = check_func func in
    let () = check_show show in
    let flags = Analysis.({
        files = files;
        func = func;
        precond = precond;
        postcond = postcond;
        trip_asserts = trip_asserts;
        check_null_derefs = check_null_derefs;
        compare_func_calls = compare_func_calls;
        compare_post_reg_values = compare_post_reg_values;
        inline = inline;
        num_unroll = num_unroll;
        gdb_output = gdb_output;
        bildb_output = bildb_output;
        use_fun_input_regs = use_fun_input_regs;
        mem_offset = mem_offset;
        debug = debug;
        stack_base = stack_base;
        stack_size = stack_size;
        show = show
      })
    in
    Analysis.run flags;
    Ok ()

end

let () =
  Cmd.declare Cli.name Cli.grammar Cli.callback ~doc:Cli.doc
