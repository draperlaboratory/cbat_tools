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
open OUnitTest

(* To run these tests: `make test` in wp directory *)

let bin_dir : string = "../resources/sample_binaries"

let timeout_msg : string = "Test times out!"

let fail_msg : string = "Test currently fails!"

let sat : string = "SAT!"

let unsat : string = "UNSAT!"

let unknown : string = "UNKNOWN!"

let check_z3_result (line : string) (expected : string) (ctxt : test_ctxt) : unit =
  if List.exists [sat; unsat; unknown] ~f:(String.equal line) then
    assert_equal
      ~ctxt
      ~printer:String.to_string
      ~cmp:String.equal
      expected line
  else
    ()

(* Given a line of input, a register, and its expected
 * value, checks if that register contains the expected value on that line.
 * Returns an error message if the line contains the register but not
 * expected value. Else returns None. *)
let check_for_match (line : string) (reg : string) (expected : string)
  : string option =
  (* Our model is printed in the form "reg |-> value".
   *  This regex will break if this changes. *)
  let pattern = Format.sprintf "^\t+%s +|-> +#[a-z0-9]$" reg in
  let re = Re.Posix.compile_pat pattern in
  if Re.execp re line then
    begin
      let re = Re.Posix.compile_pat " +" in
      let tokens = Re.split re line in
      (* Value is stored in the last index. *)
      let actual = List.last_exn tokens in
      if String.equal actual expected then
        None
      else (
        Printf.sprintf "\t%s: expected %s, got: %s\n"
          reg expected actual |> Some
      )
    end
  else None

(* Checks to see if a line of output contains a register from one of
 * the provided countermodels. If the register is in the countermodel, check
 * that the value matches what is expected for that countermodel. If matches,
 * do nothing; if does not match, append to the model's error message. *)
let check_models (line : string) (models : (string * string) list list)
    (err_msgs : (string option) list) : (string option) list =
  List.foldi models ~init:(err_msgs)
    ~f:(fun model_index err_msgs_list reg_list ->
        let result = List.fold reg_list ~init:(None)
            ~f:(fun acc (reg, expected) ->
                match acc with
                | None -> check_for_match line reg expected
                | _ -> acc ) in
        let cur_msg = List.nth_exn err_msgs_list model_index in
        let updated_err_msg =
          Option.merge ~f:(fun a b -> Printf.sprintf "%s %s" a b) cur_msg result in
        List.mapi err_msgs_list
          ~f:(fun index ele -> if index = model_index then updated_err_msg else ele))

(* Look for a line containing SAT!, UNSAT!, or UNKNOWN! in
   plugin output and compare with expected *)
let check_result (stream : char Stream.t) (expected : string)
    (expected_regs : (string * string) list list) (ctxt : test_ctxt) : unit =
  let buff = Buffer.create 16 in
  let err_msgs = List.map expected_regs ~f:( fun _ -> None) in
  let acc = ref err_msgs in
  Stream.iter (fun c ->
      match c with
      |'\n' ->
        let line = Buffer.contents buff in
        check_z3_result line expected ctxt;
        let new_err_msgs = check_models line expected_regs !acc in
        acc := new_err_msgs;
        Buffer.clear buff
      | chr ->
        Buffer.add_char buff chr)
    stream;
  let matches_a_model = List.exists !acc
      ~f:(fun ele -> ele = None) || (List.length expected_regs = 0)
  in
  if not matches_a_model then
    List.foldi !acc ~init:("") ~f:(fun index a ele ->
        match ele with
        | Some msg -> Printf.sprintf "%s \n Model %d: \n %s" a index msg
        | _ -> "" )
    |> assert_failure


(* The length of a test_case is in seconds.
   OUnit has predefined test lengths of:
   - Immediate (1.0 s)
   - Short (60.0 s)
   - Long (600.0 s)
   - Huge (1800.0 s)
     but by default, CBAT uses a custom length of 20.0 seconds. *)
let test_plugin
    ?length:(length = Custom_length 20.0)
    ?script:(script = "run_wp.sh")
    ?expected_regs:(expected_regs = [])
    (elf_dir : string)
    (expected : string)
  : test =
  let target = Format.sprintf "%s/%s" bin_dir elf_dir in
  let script = Format.sprintf "./%s" script in
  let test ctxt =
    assert_command script []
      ~foutput:(fun res -> check_result res expected expected_regs ctxt)
      ~backtrace:true
      ~chdir:target
      ~ctxt:ctxt
  in
  test_case ~length test

let test_update_num_unroll
    ?length:(length = Immediate)
    (new_unroll : int option)
  : test =
  let original = !Wp.Pre.num_unroll in
  Wp.update_default_num_unroll new_unroll;
  let updated = !Wp.Pre.num_unroll in
  let test ctxt =
    match new_unroll with
    | Some n ->
      let fail_msg =
        Format.sprintf "num_unroll was not updated from %d to %d" original n in
      assert_bool fail_msg (original <> updated)
    | None ->
      let fail_msg =
        Format.sprintf "Num unroll was updated from %d but should have been \
                        unchanged" original in
      assert_equal ~ctxt:ctxt ~cmp:Int.equal ~msg:fail_msg updated original
  in
  test_case ~length test

let test_skip (msg : string) (_ : test) (_ : test_ctxt) : unit =
  skip_if true msg


let suite = [

  (* Test elf comparison *)

  "Multicompiler: csmith"          >: test_plugin "cbat-multicompiler-samples/csmith" unsat;
  "Multicompiler: csmith inline"   >:: test_skip timeout_msg (test_plugin "cbat-multicompiler-samples/csmith" unsat
                                                                ~script:"run_wp_inline.sh");
  "Multicompiler: equiv argc"      >: test_plugin "cbat-multicompiler-samples/equiv_argc" unsat;
  "Multicompiler: switch cases"    >: test_plugin "cbat-multicompiler-samples/switch_case_assignments" unsat;

  "Diff pointer val"               >: test_plugin "diff_pointer_val" sat;
  "Diff ret val"                   >: test_plugin "diff_ret_val" sat;

  "Double dereference"             >: test_plugin "double_dereference" unsat;

  "Equiv argc"                     >: test_plugin "equiv_argc" sat
    ~expected_regs:[ [("RDI", "0x0000000000000002")]; ];
  "Precondition: force 2"          >: test_plugin "equiv_argc" sat ~script:"run_wp_force.sh"
    ~expected_regs:[ [("RDI", "0x0000000000000002")]; ];
  "Precondition: disallow 2"       >: test_plugin "equiv_argc" unsat ~script:"run_wp_disallow.sh";

  "Equiv null check"               >: test_plugin "equiv_null_check" sat;

  "Init var compare: UNSAT"        >: test_plugin "init_var_compare" unsat;
  "Init var compare: SAT"          >: test_plugin "init_var_compare" sat ~script:"run_wp_sat.sh";

  "Arrays in data section"         >: test_plugin "memory_samples/arrays" sat;
  "Arrays in data section"         >: test_plugin "memory_samples/arrays" sat ~script:"run_wp_mem_offset.sh";
  "Arrays in data section"         >: test_plugin "memory_samples/arrays" sat ~script:"run_wp_pre.sh";
  "Arrays in data section"         >: test_plugin "memory_samples/arrays" unsat ~script:"run_wp_pre_mem_offset.sh";

  "Data/BSS sections"              >: test_plugin "memory_samples/data_bss_sections" sat;
  "Data/BSS sections"              >: test_plugin "memory_samples/data_bss_sections" unsat
    ~script:"run_wp_mem_offset.sh";

  "Diff data section"              >:: test_skip fail_msg (test_plugin "memory_samples/diff_data" sat);

  "Same data, diff location"       >: test_plugin "memory_samples/diff_data_location" sat;
  "Same data, diff location"       >: test_plugin "memory_samples/diff_data_location" unsat
    ~script:"run_wp_mem_offset.sh";

  "Diff stack values"              >: test_plugin "memory_samples/diff_stack" sat;

  "Name matching"                  >: test_plugin "memory_samples/name_matching" unsat;

  "No position independent"        >: test_plugin "no_position_independent" sat;

  "No stack protection"            >: test_plugin "no_stack_protection" sat ~length:Short;

  "Null dereference: no check"     >: test_plugin "non_null_check" unsat;
  "Null dereference: with check"   >: test_plugin "non_null_check" sat ~script:"run_wp_null_deref.sh";

  "Pointer input"                  >: test_plugin "pointer_input" unsat;

  "Position independent"           >: test_plugin "position_independent" sat;

  "Retrowrite stub: pop RSP"       >: test_plugin "retrowrite_stub" unsat;
  "Retrowrite stub: inline AFL"    >: test_plugin "retrowrite_stub" unsat ~script:"run_wp_inline_afl.sh";
  "Retrowrite stub: inline all"    >: test_plugin "retrowrite_stub" unsat ~script:"run_wp_inline_all.sh";
  "Retrowrite stub no ret in call" >: test_plugin "retrowrite_stub_no_ret" unsat;

  "ROP example"                    >:: test_skip fail_msg (test_plugin "rop_example" unsat);

  "Same signs: post registers"     >: test_plugin "same_signs" unsat;
  "Same signs: postcondition"      >: test_plugin "same_signs" unsat ~script:"run_wp_postcond.sh";

  "Switch case assignments"        >: test_plugin "switch_case_assignments" sat
    ~expected_regs:[ [("RDI", "0x0000000000000000")]; ];
  "Switch Cases"                   >: test_plugin "switch_cases" sat
    ~expected_regs:[ [("RDI", "0x0000000000000003")]; ];

  "Switch Cases: Diff Ret Val"     >: test_plugin "switch_cases_diff_ret" sat
    ~expected_regs:[ [("RDI", "0x0000000000000003")]; ];

  "Indirect call with return" >: test_plugin "indirect_call_return" unsat;
  "Indirect call with no return" >: test_plugin "indirect_call_no_return" unsat;

  (* Test single elf *)

  "Function call"                  >: test_plugin "function_call" sat ~script:"run_wp_inline_foo.sh"
    ~expected_regs:[ [("RDI", "0x0000000000000005")]; ];
  "Function call: inline all"      >: test_plugin "function_call" sat ~script:"run_wp_inline_all.sh"
    ~expected_regs:[ [("RDI", "0x0000000000000005")]; ];

  "Function spec: no inlining"     >: test_plugin "function_spec" sat;
  "Function spec: inline foo"      >: test_plugin "function_spec" unsat ~script:"run_wp_inline_foo.sh";
  "Function spec: inline all "     >: test_plugin "function_spec" unsat ~script:"run_wp_inline_all.sh";
  "Function spec: inline garbage"  >: test_plugin "function_spec" sat ~script:"run_wp_inline_garbage.sh";

  "Goto string"                    >: test_plugin "goto_string" sat;
  "Goto string: inline all"        >: test_plugin "goto_string" sat ~script:"run_wp_inline.sh";

  "Init var value in post: UNSAT:" >: test_plugin "init_var" unsat;
  "Init var value in post: SAT"    >: test_plugin "init_var" sat ~script:"run_wp_sat.sh";

  "Linked list: no mem check"      >: test_plugin "linked_list" unsat;
  "Linked list: with mem check"    >: test_plugin "linked_list" sat ~script:"run_wp_null_deref.sh";

  "Loop"                           >:: test_skip fail_msg (test_plugin "loop" sat);

  "Nested function calls"               >: test_plugin "nested_function_calls" unsat;
  "Nested function calls: inline regex" >: test_plugin "nested_function_calls" sat ~script:"run_wp_inline_regex.sh"
    ~expected_regs:[ [("RDI", "0x0000000000000004")]; ];
  "Nested function calls: inline all"   >: test_plugin "nested_function_calls" sat ~script:"run_wp_inline_all.sh"
    ~expected_regs:[ [("RDI", "0x0000000000000004")]; ];

  "Nested ifs"                     >: test_plugin "nested_ifs" unsat;
  "Nested ifs: goto"               >: test_plugin "nested_ifs" unsat ~script:"run_wp_goto.sh";
  "Nested ifs: inline"             >: test_plugin "nested_ifs" unsat ~script:"run_wp_inline.sh";

  "Null dereference: no check"     >: test_plugin "null_deref" unsat;
  "Null dereference: with check"   >: test_plugin "null_deref" sat ~script:"run_wp_null_deref.sh";

  "User defined postcondition"     >: test_plugin "return_argc" sat;

  "Simple WP"                      >: test_plugin "simple_wp" sat
    ~expected_regs:[ [("RDI", "0x0000000000000003")]; ];
  "Simple WP: precondition"        >: test_plugin "simple_wp" unsat ~script:"run_wp_pre.sh";

  "Verifier assume SAT"            >: test_plugin "verifier_calls" sat ~script:"run_wp_assume_sat.sh";
  "Verifier assume UNSAT"          >: test_plugin "verifier_calls" unsat ~script:"run_wp_assume_unsat.sh";
  "Verifier nondent"               >: test_plugin "verifier_calls" sat ~script:"run_wp_nondet.sh";

  (* Test updating number of unrolls *)

  "Update Number of Unrolls"       >: test_update_num_unroll (Some 3);
  "Original Number of Unrolls"     >: test_update_num_unroll None;


  (* Test performance *)

  "Debruijn: 8 bit"                >: test_plugin "debruijn" unsat ~script:"run_wp_8bit.sh";
  "Debruijn: 16 bit"               >: test_plugin "debruijn" unsat ~script:"run_wp_16bit.sh";
  "Debruijn: 32 bit"               >: test_plugin "debruijn" unsat ~script:"run_wp_32bit.sh";
  "Debruijn: 64 bit"               >: test_plugin "debruijn" unsat ~script:"run_wp_64bit.sh";

  "NQueens solver"                 >: test_plugin "nqueens" sat ~expected_regs:[("RDI", "0x0000000000002814")];
  "Sudoku solver"                  >: test_plugin "sudoku" sat ~expected_regs:[("RDI", "0x00000000d82d7287")];

  "Hash function"                  >: test_plugin "hash_function" sat
    ~expected_regs:[("RSI", "0x0000000000000010"); ("RCX", "0x0000000000000007")];

]
