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

exception Invalid_input

type t = {
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
  show : string list
}

(* Ensures the user inputted a function for analysis. *)
let validate_func (func : string) : unit =
  if String.is_empty func then begin
    Printf.printf "Function is not provided for analysis. Usage: \
                   --func=<name>\n%!";
    raise Invalid_input
  end else
    ()

(* Looks for an invalid option among the options the user inputted. *)
let find_invalid_option (opts : string list) (valid : string list)
  : string option =
  List.find opts ~f:(fun opt ->
      not @@ List.mem valid opt ~equal:String.equal)

(* Ensures the user inputted only supported options for the debug flag. *)
let validate_debug (debug : string list) : unit =
  let valid = [
    "z3-solver-stats";
    "z3-verbose";
    "constraint-stats";
    "eval-constraint-stats"
  ] in
  match find_invalid_option debug valid with
  | Some s ->
    Printf.printf "'%s' is not a valid option for --debug. Available options \
                   are: %s\n%!" s (List.to_string valid ~f:String.to_string);
    raise Invalid_input
  | None -> ()

(* Ensures the user inputted only supported options for the show flag. *)
let validate_show (show : string list) : unit =
  let valid = [
    "bir";
    "refuted-goals";
    "paths";
    "precond-internal";
    "precond-smtlib"
  ] in
  match find_invalid_option show valid with
  | Some s ->
    Printf.printf "'%s' is not a valid option for --show. Available options \
                   are: %s\n%!" s (List.to_string valid ~f:String.to_string);
    raise Invalid_input
  | None -> ()

(* Ensures the user passed in two files to compare function calls. *)
let validate_compare_func_calls (flag : bool) (files : string list) : unit =
  if flag && (List.length files <> 2) then begin
    Printf.printf "--compare-func-calls is only used for a comparative \
                   analysis. Please specify two files. Number of files \
                   given: %d\n%!" (List.length files);
    raise Invalid_input
  end else
    ()

(* Ensures the user passed in two files to compare post register values. *)
let validate_compare_post_reg_vals (regs : string list) (files : string list)
  : unit =
  if (not @@ List.is_empty regs) && (List.length files <> 2) then begin
    Printf.printf "--compare-post-reg-values is only used for a comparative \
                   analysis. Please specify two files. Number of files \
                   given: %d\n%!" (List.length files);
    raise Invalid_input
  end else
    ()

let validate (f : t) (files : string list) : unit =
  try begin
    validate_func f.func;
    validate_compare_func_calls f.compare_func_calls files;
    validate_compare_post_reg_vals f.compare_post_reg_values files;
    validate_debug f.debug;
    validate_show f.show
  end with Invalid_input ->
    exit 1
