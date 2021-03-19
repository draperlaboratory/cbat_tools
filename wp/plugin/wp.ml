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

open Bap_main

module Parameters = Wp_parameters
module Analysis = Wp_analysis
module Cmd = Extension.Command
module Typ = Extension.Type

let name = "wp"

let doc = {|WP is a comparative analysis tool. It can compare two binaries
            and check that they behave in similar ways. It can also be used
            to check a single binary for certain behaviors.|}

(* Mandatory arguments. *)

let files = Cmd.arguments Typ.file
    ~doc:{|Path(s) to one or two binaries to analyze. If two binaries are
           specified, WP will run a comparative analysis. If 0 or more than 2
           files are given, WP will exit with an error message.|}

let func = Cmd.parameter Typ.string ~aliases:["function"] "func"
    ~doc:{|Determines which function to verify. WP verifies a single function,
           though calling it on the `main' function along with the `inline'
           option will analyze the whole program. If no function is specified
           or the function cannot be found in the binary/binaries, WP will
           exit with an error message.|}

(* Arguments that determine which properties CBAT should analyze. *)

let precond = Cmd.parameter Typ.string "precond"
    ~doc:{|Allows you to specify an assertion that WP will assume is true at
           the beginning of the function it is analyzing. Assertions are
           specified in the smt-lib2 format. For comparative predicates, one
           may refer to variables in the original and modified programs by
           appending the suffix `_orig' and `_mod' to variable names in the
           smt-lib expression. For example, `--precond="(assert (= RDI_mod
           #x0000000000000003)) (assert (= RDI_orig #x0000000000000003))".' If
           no precondition is specified, a trivial precondition of `true' will
           be used.|}

let postcond = Cmd.parameter Typ.string "postcond"
    ~doc:{|Allows you to specify an assertion that WP will assume is true at
           the end of the function it is analyzing, using the smt-lib2 format.
           Similar to `--precond', one may create comparative postconditions on
           variables by appending `_orig' and `_mod' to variable names. If no
           postcondition is specified, a trivial postcondition of `true' will
           be used.|}

let trip_asserts = Cmd.flag "trip-asserts"
    ~doc:{|Looks for inputs to the subroutine that would cause an
           `__assert_fail' or `__VERIFIER_error' to be reached.|}

let check_null_derefs = Cmd.flag "check-null-derefs"
    ~doc:{|Checks for inputs that would result in dereferencing a null value
           during a memory read or write. In the case of a comparative
           analysis, checks that the modified binary has no additional paths
           with null dereferences in comparison with the original binary.|}

let check_invalid_derefs = Cmd.flag "check-invalid-derefs"
    ~doc:{|This flag is only used in a comparative analysis. Checks that the
           modified binary has no additional paths that result in dereferences
           to invalid memory locations. That is, all memory dereferences are
           either on the stack or heap. The stack is defined as the memory
           region above the current stack pointer, and the heap is defined as
           the memory region 0x256 bytes below the lowest address of the
           stack.|}

let compare_func_calls = Cmd.flag "compare-func-calls"
    ~doc:{|This flag is only used in a comparative analysis. Checks that
           function calls do not occur in the modified binary if they have not
           occurred in the original binary.|}

let compare_post_reg_values = Cmd.parameter Typ.(list string) "compare-post-reg-values"
    ~doc:{|This flag is only used in a comparatve analysis. Compares the values
           stored in the specified registers at the end of the function's
           execution. For example, `RAX,RDI' compares the values of RAX and RDI
           at the end of execution. If unsure about which registers to compare,
           check the architecture's ABI. x86_64 architectures place their
           output in RAX, and ARM architectures place their output in R0.|}

let pointer_reg_list = Cmd.parameter Typ.(list string) "pointer-reg-list"
    ~doc:{|This flag specifies a comma delimited list of input registers to be
           treated as pointers at the start of program execution. This means
           that these registers are restricted in value to point to memory
           known to be initialized at the start of the function. For example,
           `RSI,RDI` would specify that `RSI` and `RDI`'s values should be
           restricted to initialized memory at the start of execution.|}

(* Options. *)

let inline = Cmd.parameter Typ.(some string) "inline"
    ~doc:{|Functions specified by the provided POSIX regular expression will be
           inlined. When functions are not inlined, heuristic function
           summaries are used at function call sites. For example, if you want
           to inline the functions `foo' and `bar', you can write
           `--inline=foo|bar'. To inline everything, use `--inline=.*' (not
           generally recommended).|}

let num_unroll = Cmd.parameter Typ.(some int) "num-unroll"
    ~doc:{|Specifies the number of times to unroll each loop. WP will unroll
           each loop 5 times by default.|}

let gdb_output = Cmd.parameter Typ.(some string) "gdb-output"
    ~doc:{|When WP results in SAT, outputs a gdb script to the filename
           specified. From within gdb, run `source filename.gdb' to set a
           breakpoint at the function given by `--func' and fill the
           appropriate registers with the values found in the countermodel. In
           the case WP returns UNSAT or UNKNOWN, no script will be outputted.|}

let bildb_output = Cmd.parameter Typ.(some string) "bildb-output"
    ~doc:{|When WP results in SAT, outputs a BILDB initialization script to the
           filename specified. This YAML file sets the registers and memory to
           the values found in the countermodel, allowing BILDB to follow the
           same execution trace. In the case WP returns UNSAT or UNKNOWN, no
           script will be outputted.|}

let use_fun_input_regs = Cmd.flag "use-fun-input-regs"
    ~doc:{|At a function call site, uses all possible input registers as
           arguments to a function symbol generated for an output register. If
           this flag is not present, no registers will be used.|}

let mem_offset = Cmd.flag "mem-offset"
    ~doc:{|This flag is only used in a comparative analysis. Maps the symbols
           in the data and bss sections from their addresses in the original
           binary to their addresses in the modified binary. If this flag is
           not present, WP assumes that memory between both binaries start at
           the same offset.|}

let rewrite_addresses = Cmd.flag "rewrite-addresses"
    ~doc:{|This flag is only used in a comparative analysis. Rewrites the
           concrete addresses in the modified binary to the same address in the
           original binary if they point to the same symbol. This flag should
           not be used in conjunction with the `--mem-offset' flag.|}

let debug = Cmd.parameter Typ.(list string) "debug"
    ~doc:{|A list of various debugging statistics to display. Multiple
           statistics may be specified in a comma-separated list. For example:
           `--debug=z3-solver-stats,z3-verbose'. The options are:

           `z3-solver-stats': Information and statistics about Z3's solver.
           It includes information such as the maximum amount of memory used
           and the number of allocations.

           `z3-verbose': Z3's verbosity level. It outputs information such as
           the tactics the Z3 solver used.

           `constraint-stats': Statistics regarding the internal `Constr.t'
           data structure, including the number of goals, ITEs, clauses, and
           substitutions.

           `eval-constraint-stats': Statistics regarding the internal
           expression lists during evaluation of the `Constr.t' data type.|}

let show = Cmd.parameter Typ.(list string) "show"
    ~doc:{|A list of details to print out from the analysis. Multiple options
           can be specified as a comma-separated list. For example:
           `--show=bir,refuted-goals'. The options are:

           `bir': The code of the binary/binaries in BAP Intermediate
           Representation.

           `refuted-goals': In the case WP results in SAT, a list of goals
           refuted in the model that contains their tagged names, their
           concrete values, and their Z3 representation.

           `paths': The execution path of the binary that results in a
           refuted goal. The path contains information about the jumps taken,
           their addresses, and the values of the registers at each jump.
           This option automatically prints out the refuted goals.

           `precond-smtlib': The precondition printed out in Z3's SMT-LIB2
           format.

           `precond-internal': The precondition printed out in WP's internal
           format for the `Constr.t' type.|}

let stack_base = Cmd.parameter Typ.(some int) "stack-base"
    ~doc:{|Sets the location of the stack frame for the function under
           analysis. By default, WP assumes the stack frame for the current
           function is between 0x40000000 and 0x3F800080.|}

let stack_size = Cmd.parameter Typ.(some int) "stack-size"
    ~doc:{|Sets the size of the stack, which should be denoted in bytes. By
           default, the size of the stack is 0x800000 which is 8MB.|}

let func_name_map = Cmd.parameter Typ.(list ~sep:';' (pair ~sep:',' string string))
    "func-name-map"
    ~doc:{|Maps the subroutine names from the original binary to their names in
           the modified binary based on the regex from the user. Usage:
           --func-name-map="<regex for original name>,<regex for modified name>".
           For example: --func-name-map="\\(.*\\),foo_\\1" means that all
           subroutines in the original binary have foo_ prepended in the
           modified binary. Multiple patterns can be used to map function names
           and are delimited with ';'s (i.e.
           "<reg1_orig>,<reg1_mod>;<reg2_orig>,<reg2_mod>"). By default, WP
           assumes subroutines have the same names between the two binaries.|}

let user_func_spec = Cmd.parameter Typ.(some (t3 string string string)) "user-func-spec"
    ~doc:{|Creates the weakest precondition for a subroutine given the
           name of the subroutine and its pre and post-conditions. Usage:
           --user-func-spec="<sub name>,<precondition>,<postcondition>". For example,
           --user-func-spec="foo,(assert (= RAX RDI)),(assert (= RAX init_RDI)"
           means "for subroutine named foo, specify that its precondition is
           RAX = RDI and its postcondition is RAX = init_RDI".|}

let fun_specs = Cmd.parameter Typ.(list string) "fun-specs"
    ~doc:{|List of built-in function summaries to be used at a function call
           site in order of precedence. A target function will be mapped to a
           function spec if it fulfills the spec's requirements. All function
           specs set the target function as called and update the stack
           pointer. The default specs set are verifier-assume, varifier-nondet,
           empty, and chaos-caller-saved. Note that if a function is set to be
           inlined, it will not use any of the following function specs.
           Available built-in specs:

           `verifier-error': Used for calls to __VERIFIER_error and
           __assert_fail. Looks for inputs that would cause execution to reach
           these functions.

           `verifier-assume': Used for calls to __VERIFIER_assume. Adds an
           assumption to the precondition based on the argument to the function
           call.

           `verifier-nondet': Used for calls to nondeterministic functions such
           as __VERIFIER_nondet_*, calloc, and malloc. Chaoses the output to
           the function call representing an arbitrary pointer.

           `afl-maybe-log': Used for calls to __afl_maybe_log. Chaoses the
           registers RAX, RCX, and RDX.

           `arg-terms': Used when BAP's uplifter returns a nonempty list of
           input and output registers for the target function. Chaoses this
           list of output registers.

           `chaos-caller-saved': Used for the x86 architecture. Chaoses the
           caller-saved registers.

           `rax-out': Chaos RAX if it can be found on the left-hand side of an
           assignment in the target function.

           `chaos-rax': Chaos RAX regardless if it has been used on the
           left-hand side of an assignment in the target function.

           `empty': Used for empty subroutines. Performs no actions.|}
let ext_solver_path = Cmd.parameter Typ.(some string) "ext-solver-path"
    ~doc:{|Path of external smt solver to call. Boolector recommended. |}

let loop_invariant = Cmd.parameter Typ.(some string) "loop-invariant"
    ~doc:{|Assumes the subroutine contains a single unnested loop with one entrance
           and one exit. Checks the specified loop invariant written in
           smt-lib2 format.|}

let grammar = Cmd.(
    args
    $ func
    $ precond
    $ postcond
    $ trip_asserts
    $ check_null_derefs
    $ check_invalid_derefs
    $ compare_func_calls
    $ compare_post_reg_values
    $ pointer_reg_list
    $ inline
    $ num_unroll
    $ loop_invariant
    $ gdb_output
    $ bildb_output
    $ use_fun_input_regs
    $ mem_offset
    $ rewrite_addresses
    $ debug
    $ show
    $ stack_base
    $ stack_size
    $ func_name_map
    $ user_func_spec
    $ fun_specs
    $ ext_solver_path
    $ files)

(* The callback run when the command is invoked from the command line. *)
let callback
    (func : string)
    (precond : string)
    (postcond : string)
    (trip_asserts : bool)
    (check_null_derefs : bool)
    (check_invalid_derefs : bool)
    (compare_func_calls : bool)
    (compare_post_reg_values : string list)
    (pointer_reg_list : string list)
    (inline : string option)
    (num_unroll : int option)
    (loop_invariant : string option)
    (gdb_output : string option)
    (bildb_output : string option)
    (use_fun_input_regs : bool)
    (mem_offset : bool)
    (rewrite_addresses : bool)
    (debug : string list)
    (show : string list)
    (stack_base : int option)
    (stack_size : int option)
    (func_name_map : (string * string) list)
    (user_func_spec : (string*string*string) option)
    (fun_specs : string list)
    (ext_solver_path : string option)
    (files : string list)
    (ctxt : ctxt) =
  let open Parameters.Err.Syntax in
  let params = Parameters.({
      func = func;
      precond = precond;
      postcond = postcond;
      trip_asserts = trip_asserts;
      check_null_derefs = check_null_derefs;
      check_invalid_derefs = check_invalid_derefs;
      compare_func_calls = compare_func_calls;
      compare_post_reg_values = compare_post_reg_values;
      pointer_reg_list = pointer_reg_list;
      inline = inline;
      num_unroll = num_unroll;
      loop_invariant = loop_invariant;
      gdb_output = gdb_output;
      bildb_output = bildb_output;
      use_fun_input_regs = use_fun_input_regs;
      mem_offset = mem_offset;
      rewrite_addresses = rewrite_addresses;
      debug = debug;
      show = show;
      stack_base = stack_base;
      stack_size = stack_size;
      func_name_map = func_name_map;
      user_func_spec = user_func_spec;
      fun_specs = fun_specs;
      ext_solver_path = ext_solver_path;
    })
  in
  Parameters.validate params files >>= fun () ->
  Analysis.run params files ctxt >>= fun () ->
  Ok ()

let () =
  Cmd.declare name grammar callback ~doc
