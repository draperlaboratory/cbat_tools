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

let test_plugin
    ?script:(script = "run_wp.sh")
    (elf_dir : string)
    (expected : string)
    (test_ctx : test_ctxt)
    : unit =
  let target = Format.sprintf "%s/%s" bin_dir elf_dir in
  let script = Format.sprintf "./%s" script in
  assert_command ~foutput:(fun res -> check_result res expected test_ctx)
    ~backtrace:true ~chdir:target ~ctxt:test_ctx script []

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

  (* Test elf comparison *)
  "Multicompiler: csmith"          >:: test_plugin "cbat-multicompiler-samples/csmith" "UNSAT!";
  "Multicompiler: csmith inline"   >:: test_plugin "cbat-multicompiler-samples/csmith" "UNSAT!"
    ~script:"run_wp_inline.sh"; (* fails! *)
  "Multicompiler: equiv argc"      >:: test_plugin "cbat-multicompiler-samples/equiv_argc" "UNSAT!";
  "Multicompiler: switch cases"    >:: test_plugin "cbat-multicompiler-samples/switch_case_assignments" "UNSAT!";

  "Diff pointer val"               >:: test_plugin "diff_pointer_val" "SAT!";
  "Diff ret val"                   >:: test_plugin "diff_ret_val" "SAT!";
  "Double dereference"             >:: (fun ctx -> skip_if true "times out"; test_plugin "double_dereference" "UNSAT!" ctx);
  "Equiv argc"                     >:: test_plugin "equiv_argc" "SAT!";
  "Precondition: force 2"          >:: test_plugin "equiv_argc" "SAT!" ~script:"run_wp_force_2.sh";
  "Precondition: disallow 2"       >:: test_plugin "equiv_argc" "UNSAT!" ~script:"run_wp_disallow_2.sh";
  "Equiv null check"               >:: test_plugin "equiv_null_check" "SAT!";

  "Init var compare: UNSAT"        >:: test_plugin "init_var_compare" "UNSAT!";
  "Init var compare: SAT"          >:: test_plugin "init_var_compare" "SAT!" ~script:"run_wp_sat.sh";

  "Arrays in sata section"         >:: test_plugin "memory_samples/arrays" "SAT!";
  "Arrays in data section"         >:: test_plugin "memory_samples/arrays" "SAT!" ~script:"run_wp_mem_offset.sh";
  "Arrays in data section"         >:: test_plugin "memory_samples/arrays" "SAT!" ~script:"run_wp_pre.sh";
  "Arrays in data section"         >:: test_plugin "memory_samples/arrays" "UNSAT!" ~script:"run_wp_pre_mem_offset.sh";

  "Data/BSS sections"              >:: test_plugin "memory_samples/data_bss_sections" "SAT!";
  "Data/BSS sections"              >:: test_plugin "memory_samples/data_bss_sections" "UNSAT!"
    ~script:"run_wp_mem_offset.sh";

  "Diff data section"              >:: test_plugin "memory_samples/diff_data" "SAT!"; (* fails *)

  "Same data, diff location"       >:: test_plugin "memory_samples/diff_data_location" "SAT!";
  "Same data, diff location"       >:: test_plugin "memory_samples/diff_data_location" "UNSAT!"
    ~script:"run_wp_mem_offset.sh";

  "Diff stack values"              >:: test_plugin "memory_samples/diff_stack" "SAT!";

  "No Stack Protection"            >:: test_plugin "no_stack_protection" "SAT!";
  "Pointer input" >:: (fun ctx -> skip_if true "not added"; test_plugin "pointer_input" "UNSAT!" ctx);

  "Retrowrite Stub: pop RSP"       >:: test_plugin "retrowrite_stub" "UNSAT!";
  "Retrowrite Stub: inline AFL"    >:: test_plugin "retrowrite_stub" "UNSAT!" ~script:"run_wp_inline_afl.sh";
  "Retrowrite Stub: inline all"    >:: test_plugin "retrowrite_stub" "UNSAT!" ~script:"run_wp_inline_all.sh";
  "Retrowrite Stub No Ret in Call" >:: test_plugin "retrowrite_stub_no_ret" "UNSAT!";

  "ROP example"                    >:: test_plugin "rop_example" "UNSAT!"; (* fails *)
  "Switch case assignments"        >:: test_plugin "switch_case_assignments" "SAT!";
  "Switch Cases"                   >:: test_plugin "switch_cases" "SAT!";

  (* Test single elf *)
  "Function Call"                  >:: test_plugin "function_call" "SAT!" ~script:"run_wp_inline_foo.sh";
  "Function Call: inline all"      >:: test_plugin "function_call" "SAT!" ~script:"run_wp_inline_all.sh";
  "Function Spec: no inlining"     >:: test_plugin "function_spec" "SAT!";
  "Function Spec: inline foo"      >:: test_plugin "function_spec" "UNSAT!" ~script:"run_wp_inline_foo.sh";
  "Function Spec: inline all "     >:: test_plugin "function_spec" "UNSAT!" ~script:"run_wp_inline_all.sh";
  "Function Spec: inline garbage"  >:: test_plugin "function_spec" "SAT!" ~script:"run_wp_inline_garbage.sh";

  "Goto string"                    >:: (fun ctx -> skip_if true "not added"; test_plugin "goto_string" "SAT!" ctx);
  "Goto string: inline all"        >:: (fun ctx -> skip_if true "not added"; test_plugin "goto_string" "SAT!"
                                    ~script:"run_wp_inline.sh" ctx);

  "Init var value in post: UNSAT:" >:: test_plugin "init_var" "UNSAT!";
  "Init var value in post: SAT"    >:: test_plugin "init_var" "SAT!" ~script:"run_wp_sat.sh";

  "Nested function calls"               >:: test_plugin "nested_function_calls" "UNSAT!";
  "Nested function calls: inline regex" >:: test_plugin "nested_function_calls" "SAT!" ~script:"run_wp_inline_regex.sh";
  "Nested function calls: inline all"   >:: test_plugin "nested_function_calls" "SAT!" ~script:"run_wp_inline_all.sh";

  "Nested ifs"                     >:: test_plugin "nested_ifs" "UNSAT!";
  "Nested ifs: inline"             >:: test_plugin "nested_ifs" "UNSAT!" ~script:"run_wp_inline.sh";

  "User defined postcondition"     >:: test_plugin "return_argc" "SAT!";

  "Simple WP"                      >:: test_plugin "simple_wp" "SAT!";
  "Simple WP: precondition"        >:: test_plugin "simple_wp" "UNSAT!" ~script:"run_wp_pre.sh";

  "Verifier assume SAT"            >:: test_plugin "verifier_calls" "SAT!" ~script:"run_wp_assume_sat.sh";
  "Verifier assume UNSAT"          >:: test_plugin "verifier_calls" "UNSAT!" ~script:"run_wp_assume_unsat.sh";
  "Verifier nondent"               >:: test_plugin "verifier_calls" "SAT!" ~script:"run_wp_nondet.sh";

  "Update Number of Unrolls"       >:: test_update_num_unroll (Some 3);
  "Original Number of Unrolls"     >:: test_update_num_unroll None;
]
