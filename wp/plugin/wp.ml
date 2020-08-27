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

let doc = "WP is a comparative analysis tool. It can compare two binaries \
           and check that they behave in similar ways. It can also be used \
           to check a single binary for certain behaviors."

(* Mandatory arguments. *)

let files = Cmd.arguments Typ.file
    ~doc:"Path(s) to one or two binaries to analyze. If two binaries are \
          specified, WP will run a comparative analysis."

let func = Cmd.parameter Typ.string ~aliases:["function"] "func"
    ~doc:"Function to run the WP analysis on. If no function is specified or \
          the function cannot be found in the binaries, the analysis will \
          fail."

(* Arguments that determine which properties CBAT should analyze. *)

let precond = Cmd.parameter Typ.string "precond"
    ~doc:"A custom precondition in SMT-LIB format to be used during the \
          analysis. If no precondition is specified, a trivial precondition \
          of `true' will be used."

let postcond = Cmd.parameter Typ.string "postcond"
    ~doc:"A custom postcondition in SMT-LIB format to be used during the \
          analysis. If no postcondition is specified, a trivial \
          postcondition of `true' will be used."

let trip_asserts = Cmd.flag "trip-asserts"
    ~doc:"If set, WP will look for inputs to the subroutine that would cause \
          an __assert_fail or __VERIFIER_error to be reached."

let check_null_derefs = Cmd.flag "check-null-derefs"
    ~doc:"If set, the WP analysis will check for inputs that would result in \
          dereferencing a NULL value. In the case of a comparative analysis, \
          WP will check that the modified binary has no additional null \
          dereferences in comparison with the original binary."

let compare_func_calls = Cmd.flag "compare-func-calls"
    ~doc:"This flag is used for a comparative analysis. If set, WP will \
          check that function calls should not occur in the modified binary \
          if they have not occurred in the original binary."

let compare_post_reg_values = Cmd.parameter Typ.(list string) "compare-post-reg-values"
    ~doc:"This flag is used for a comparatve analysis. If set, WP will \
          compare the values stored in the specified registers at the end of \
          the analyzed function's execution. For example, `RAX,RDI' compares \
          the values of RAX and RDI at the end of execution. If unsure about \
          which registers to compare, x86_64 architectures place their \
          output in RAX, and ARM architectures place their output in R0."

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
          goal, this flag outputs a gdb script to the filename specified. \
          This script file sets a breakpoint at the the start of the \
          function being analyzed, and sets the registers and memory to the \
          values specified in the countermodel, allowing GDB to follow the \
          same execution trace."

let bildb_output = Cmd.parameter Typ.(some string) "bildb-output"
    ~doc:"In the case WP determines input registers that result in a refuted \
          goal, this flag outputs a BilDB YAML file to the filename \
          specified. This file sets the registers and memory to the values \
          specified in the countermodel, allowing BilDB to follow the same \
          execution trace."

let use_fun_input_regs = Cmd.flag "use-fun-input-regs"
    ~doc:"If set, at a function call site, uses all possible input registers \
          as arguments to a function symbol generated for an output register \
          that represents the result of the function call. If this flag is not \
          set, no registers will be used."

let mem_offset = Cmd.flag "mem-offset"
    ~doc:"If set, maps the symbols in the data and bss sections from their \
          addresses in the original binary to their addresses in the \
          modified binary."

let debug = Cmd.parameter Typ.(list string) "debug"
    ~doc:{|A list of various debugging statistics to print out during the
           analysis. Multiple options as a list can be passed into the flag
           to print multiple statistics. For example:
           `--debug=z3-solver-stats,z3-verbose'.

           The options are:
           `z3-solver-stats': Statistics about the Z3 solver including
           information such as the maximum amount of memory used and the number
           of allocations.

           `z3-verbose': Increases Z3's verbosity level to output information
           during precondition check time including the tactics the solver used.

           `constraint-stats': Prints out the number of goals, ITES, clauses,
           and substitutions in the constraint data type of the precondition.

           `eval-constraint-stats': Prints out the mean, max, and standard
           deviation of the number of substitutions that occur during the
           evaluation of the constraint datatype.|}

let show = Cmd.parameter Typ.(list string) "show"
    ~doc:{|A list of details to print out from the analysis. Multiple options
           as a list can be passed into the flag to print out multiple
           details. For example: `--show=bir,refuted-goals'.

           The options are:
           `bir': The code of the binary/binaries in BAP Immediate
           Representation.

           `refuted-goals': In the case the analysis results in SAT, a list
           of goals refuted in the model that contains their tagged names,
           the concrete values of the goals, and the Z3 representation of the
           goal.

           `paths': The execution path of the binary that results in a
           refuted goal. The path contains information about the jumps taken,
           their addresses, and the values of the registers at each jump.
           This option automatically prints out the refuted goals.

           `precond-internal': The precondition printed out in WP's internal
           format for the Constr.t type.

          `precond-smtlib': The precondition printed out in Z3's SMT-LIB2
           format.|}

let stack_base = Cmd.parameter Typ.(some int) "stack-base"
    ~doc:"The default address of the stack base. WP assumes the stack base \
          is the highest address and the stack grows downward. By default, \
          set to 0x40000000."

let stack_size = Cmd.parameter Typ.(some int) "stack-size"
    ~doc:"The default size of the stack in bytes. By default, set to \
          0x800000 which is 8Mbs."

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
