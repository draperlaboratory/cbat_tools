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
open OUnit2

(* To run these tests: `make test` in wp directory *)

let bin_dir = "../resources/sample_binaries"

let is_z3_result (res : string) : bool =
  match res with
  | "SAT!" | "UNSAT!" | "UNKNOWN!" -> true
  | _ -> false

(* Look for a line containing SAT!, UNSAT!, or UNKNOWN! in
   plugin output and compare with expected *)
let check_result (stream : char Stream.t) (expected : string) (test_ctx : test_ctxt) : unit =
  let buff = Buffer.create 16 in
  Stream.iter (function
      |'\n' ->
        let line = Buffer.contents buff in
        if is_z3_result line then
          assert_equal ~ctxt:test_ctx
            ~printer:(fun s -> s)
            ~cmp:String.equal
            expected line;
        Buffer.clear buff
      | chr -> Buffer.add_char buff chr)
    stream

let test_compare_elf (elf_dir : string) (expected : string)
    ?func:(func = "main")
    ?check_calls:(check_calls = false)
    ?inline:(inline = "")
    ?output_vars:(output_vars = "RAX,EAX")
    (test_ctx : test_ctxt)
  : unit =
  let target = Format.sprintf "%s/%s" bin_dir elf_dir in
  let args =
    [ Format.sprintf "%s/dummy/hello_world.out" bin_dir;
      Format.sprintf "--pass=%s" "wp";
      Format.sprintf "--wp-compare=%b" true;
      Format.sprintf "--wp-file1=%s/main_1.bpj" target;
      Format.sprintf "--wp-file2=%s/main_2.bpj" target;
      Format.sprintf "--wp-function=%s" func;
      Format.sprintf "--wp-check-calls=%b" check_calls;
      Format.sprintf "--wp-inline=%s" inline;
      Format.sprintf "--wp-output-vars=%s" output_vars;
    ] in
  assert_command ~backtrace:true ~ctxt:test_ctx "make" ["-C"; target];
  assert_command ~foutput:(fun res -> check_result res expected test_ctx)
    ~backtrace:true ~ctxt:test_ctx "bap" args

let test_single_elf (elf_dir : string) (elf_name : string) (expected : string)
    ?func:(func = "main")
    ?check_calls:(check_calls = false)
    ?inline:(inline = "")
    ?post:(post = "")
    (test_ctx : test_ctxt)
  : unit =
  let target = Format.sprintf "%s/%s" bin_dir elf_dir in
  let args =
    [ Format.sprintf "%s/%s" target elf_name;
      Format.sprintf "--pass=%s" "wp";
      Format.sprintf "--wp-compare=%b" false;
      Format.sprintf "--wp-function=%s" func;
      Format.sprintf "--wp-check-calls=%b" check_calls;
      Format.sprintf "--wp-inline=%s" inline;
      Format.sprintf "--wp-postcond=%s" post;
    ] in
  assert_command ~backtrace:true ~ctxt:test_ctx "make" ["-C"; target; elf_name];
  assert_command ~foutput:(fun res -> check_result res expected test_ctx)
    ~backtrace:true ~ctxt:test_ctx "bap" args

let test_update_num_unroll (new_unroll : int option) (test_ctx : test_ctxt) : unit =
  let original = !Wp.Pre.num_unroll in
  Wp.update_default_num_unroll new_unroll;
  let updated = !Wp.Pre.num_unroll in
  match new_unroll with
  | Some n ->
    let fail_msg = Format.sprintf "num_unroll was not updated from %d to %d" original n in
    assert_bool fail_msg (original <> updated)
  | None ->
    let fail_msg = Format.sprintf "Num unroll was updated from %d but should have been unchanged" original in
    assert_equal ~ctxt:test_ctx ~cmp:Int.equal ~msg:fail_msg updated original

let suite = [
  "Equiv Null Check"               >:: test_compare_elf "equiv_null_check" "SAT!";
  "Equiv Argc"                     >:: test_compare_elf "equiv_argc" "SAT!";
  "Diff Ret Val"                   >:: test_compare_elf "diff_ret_val" "SAT!";
  "Diff Pointer Val"               >:: test_compare_elf "diff_pointer_val" "SAT!";
  "Switch Case Assignments"        >:: test_compare_elf "switch_case_assignments" "SAT!" ~func:"process_status";
  "Switch Cases"                   >:: test_compare_elf "switch_cases" "SAT!" ~func:"process_message" ~check_calls:true;
  "No Stack Protection"            >:: test_compare_elf "no_stack_protection" "SAT!" ~output_vars:"RSI,RAX";
  "Retrowrite Stub"                >:: test_compare_elf "retrowrite_stub" "UNSAT!" ~inline:"__afl_maybe_log";
  "Retrowrite Stub: inline all"    >:: test_compare_elf "retrowrite_stub" "UNSAT!" ~inline:".*";
  "Retrowrite Stub: Pop RSP"       >:: test_compare_elf "retrowrite_stub" "UNSAT!";
  "Retrowrite Stub No Ret in Call" >:: test_compare_elf "retrowrite_stub_no_ret" "UNSAT!";

  "Simple WP"                      >:: test_single_elf "simple_wp" "main" "SAT!";
  "Verifier Assume SAT"            >:: test_single_elf "verifier_calls" "verifier_assume_sat" "SAT!";
  "Verifier Assume UNSAT"          >:: test_single_elf "verifier_calls" "verifier_assume_unsat" "UNSAT!";
  "Verifier Nondet"                >:: test_single_elf "verifier_calls" "verifier_nondet" "SAT!";
  "Function Call"                  >:: test_single_elf "function_call" "main" "SAT!" ~inline:"foo";
  "Function Call: inline all"      >:: test_single_elf "function_call" "main" "SAT!" ~inline:".*";
  "Function Spec"                  >:: test_single_elf "function_spec" "main" "UNSAT!" ~inline:"foo";
  "Function Spec: inline all "     >:: test_single_elf "function_spec" "main" "UNSAT!" ~inline:".*";
  "Function Spec: no inlining"     >:: test_single_elf "function_spec" "main" "SAT!" ~inline:"NONEXISTENTGARBAGE";
  "Nested Function Calls"          >:: test_single_elf "nested_function_calls" "main" "SAT!" ~inline:"foo|bar";
  "Nested Calls: inline all"       >:: test_single_elf "nested_function_calls" "main" "SAT!" ~inline:".*";
  "User Defined Postcondition"     >:: test_single_elf "return_argc" "main" "SAT!" ~post:"(assert (= RAX #x0000000000000000))";

  "Update Number of Unrolls"       >:: test_update_num_unroll (Some 3);
  "Original Number of Unrolls"     >:: test_update_num_unroll None;
]
