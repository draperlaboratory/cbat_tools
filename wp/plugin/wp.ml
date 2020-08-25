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
open Parameters.Err.Syntax

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
           files are give, WP will fail.|}

let func = Cmd.parameter Typ.string ~aliases:["function"] "func"
    ~doc:{|Determines which function to verify. WP verifies a single function,
           though calling it on the `main' function along with the `inline'
           option will analyze the whole program. If no function is specified
           or the function cannot be found in the binary/binaries, the analysis
           will fail.|}

(* Arguments that determine which properties CBAT should analyze. *)

let precond = Cmd.parameter Typ.string "precond"
    ~doc:{|Allows the introduction of assertions to the beginning of a query.
           This allows pruning of possible models. Assertions are specified in
           the smt-lib2 format. For comparative predicates, one may refer to
           variables in the original and modified programs by appending the
           suffix `_orig' and `_mod' to variable names in the smt-lib
           expression. For example, `--precond="(assert (= RDI_mod
           #x0000000000000003)) (assert (= RDI_orig #x0000000000000003))".' If
           no precondition is specified, a trivial precondition of `true' will
           be used.|}

let postcond = Cmd.parameter Typ.string "postcond"
    ~doc:{|Replaces the default postcondition with the user-specified one,
           using the smt-lib2 format. Similar to `--precond', one may create
           comparative postconditions on variables by appending `_orig' and
           `_mod' to variable names. If no postcondition is specified, a
           trivial postcondition of `true' will be used.|}

let trip_asserts = Cmd.flag "trip-asserts"
    ~doc:{|Looks for inputs to the subroutine that would cause an
           `__assert_fail' or `__VERIFIER_error' to be reached.|}

let check_null_derefs = Cmd.flag "check-null-derefs"
    ~doc:{|Checks for inputs that would result in dereferencing a null value
           during a memory read or write. In the case of a comparative
           analysis, checks that the modified binary has no additional null
           dereferences in comparison with the original binary.|}

let compare_func_calls = Cmd.flag "compare-func-calls"
    ~doc:{|This flag is only used in a comparative analysis. Checks that
           function calls do not occur in the modified binary if they have not
           occurred in the original binary.|}

let compare_post_reg_values = Cmd.parameter Typ.(list string) "compare-post-reg-values"
    ~doc:{|This flag is only used in a comparatve analysis. Compares the values
           stored in the specified registers at the end of the function's
           execution. For example, `RAX,RDI' compares the values of RAX and RDI
           at the end of execution. If unsure about which registers to compare,
           x86_64 architectures place their output in RAX, and ARM
           architectures place their output in R0.|}

(* Options. *)

let inline = Cmd.parameter Typ.(some string) "inline"
    ~doc:{|Functions specified by the provided POSIX regular expression will be
           inlined. When functions are not inlined, heuristic function
           summaries are used at function call sites. For example, if you want
           to inline the functions `foo' and `bar', you can write
           `--inline=foo|bar'. To inline everything, use `--inline=.*' (not
           generally recommended).|}

let num_unroll = Cmd.parameter Typ.(some int) "num-unroll"
    ~doc:{|Replaces the default number of times to unroll each loop. WP will
           unroll each loop 5 times by default.|}

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
           not present, WP assumes that memory between both binaries are
           equal.|}

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
           data structure, including the number of goals, ITES, clauses, and
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
      $ show
      $ stack_base
      $ stack_size
      $ files)

(* The callback run when the command is invoked from the command line. *)
let callback
    (func : string)
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
    (show : string list)
    (stack_base : int option)
    (stack_size : int option)
    (files : string list)
    (ctxt : ctxt) =
  let params = Parameters.({
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
      show = show;
      stack_base = stack_base;
      stack_size = stack_size
    })
  in
  Parameters.validate params files >>= fun () ->
  Analysis.run params files ctxt >>= fun () ->
  Ok ()

let () =
  Cmd.declare name grammar callback ~doc
