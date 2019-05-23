(***************************************************************************)
(*                                                                         *)
(*  Copyright (C) 2018 The Charles Stark Draper Laboratory, Inc.           *)
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

let bin_dir = "./resources/sample_binaries"

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

let test_compare_elf (elf_dir : string) (expected : string) ?func:(func = "main")
    ?check_calls:(check_calls = false) (test_ctx : test_ctxt) : unit =
  let target = Printf.sprintf "%s/%s" bin_dir elf_dir in
  let args =
    [ Printf.sprintf "%s/dummy/hello_world.out" bin_dir;
      Printf.sprintf "--pass=%s" "wp";
      Printf.sprintf "--wp-compare=%b" true;
      Printf.sprintf "--wp-file1=%s/main_1.bpj" target;
      Printf.sprintf "--wp-file2=%s/main_2.bpj" target;
      Printf.sprintf "--wp-function=%s" func;
      Printf.sprintf "--wp-check-calls=%b" check_calls;
    ] in
  assert_command ~backtrace:true ~ctxt:test_ctx "make" ["-C"; target];
  assert_command ~foutput:(fun res -> check_result res expected test_ctx)
    ~backtrace:true ~ctxt:test_ctx "bap" args;
  assert_command ~backtrace:true ~ctxt:test_ctx "make" ["-C"; target; "clean"]

let test_single_elf (elf_dir : string) (elf_name : string) (expected : string)
    ?func:(func = "main")
    ?check_calls:(check_calls = false)
    ?inline:(inline = false)
    ?post:(post = "")
    (test_ctx : test_ctxt)
  : unit =
  let target = Printf.sprintf "%s/%s" bin_dir elf_dir in
  let args =
    [ Printf.sprintf "%s/%s" target elf_name;
      Printf.sprintf "--pass=%s" "wp";
      Printf.sprintf "--wp-compare=%b" false;
      Printf.sprintf "--wp-function=%s" func;
      Printf.sprintf "--wp-check-calls=%b" check_calls;
      Printf.sprintf "--wp-inline=%b" inline;
      Printf.sprintf "--wp-postcond=%s" post;
    ] in
  assert_command ~backtrace:true ~ctxt:test_ctx "make" ["-C"; target; elf_name];
  assert_command ~foutput:(fun res -> check_result res expected test_ctx)
    ~backtrace:true ~ctxt:test_ctx "bap" args;
  with_bracket_chdir test_ctx target
    (fun ctxt -> assert_command ~backtrace:true ~ctxt "rm" ["-f"; elf_name])

let suite = [
  "Equiv Null Check"           >:: test_compare_elf "equiv_null_check" "SAT!";
  "Equiv Argc"                 >:: test_compare_elf "equiv_argc" "SAT!";
  "Diff Ret Val"               >:: test_compare_elf "diff_ret_val" "SAT!";
  "Diff Pointer Val"           >:: test_compare_elf "diff_pointer_val" "SAT!";
  "Switch Case Assignments"    >:: test_compare_elf "switch_case_assignments" "SAT!" ~func:"process_status";
  "Switch Cases"               >:: test_compare_elf "switch_cases" "SAT!" ~func:"process_message" ~check_calls:true;
  "Remove Stack Protector"     >:: test_compare_elf "no_stack_protection" "SAT!";
  "Simple WP"                  >:: test_single_elf "simple_wp" "main" "SAT!";
  "Verifier Assume SAT"        >:: test_single_elf "verifier_calls" "verifier_assume_sat" "SAT!";
  "Verifier Assume UNSAT"      >:: test_single_elf "verifier_calls" "verifier_assume_unsat" "UNSAT!";
  "Verifier Nondet"            >:: test_single_elf "verifier_calls" "verifier_nondet" "SAT!";
  "Function Call"              >:: test_single_elf "function_call" "main" "SAT!" ~inline:true;
  "Nested Function Calls"      >:: test_single_elf "nested_function_calls" "main" "SAT!" ~inline:true;
  "User Defined Postcondition" >:: test_single_elf "return_argc" "main" "SAT!" ~post:"(assert (= RAX0 #x0000000000000000))";
]
