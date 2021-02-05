open OUnitTest
open Test_wp_utils

let unit_tests = [

  (* Test elf comparison *)

  "Multicompiler: csmith"          >: test_plugin "cbat-multicompiler-samples/csmith" unsat;
  "Multicompiler: csmith inline"   >:: test_skip timeout_msg (test_plugin "cbat-multicompiler-samples/csmith" unsat
                                                                ~script:"run_wp_inline.sh");
  "Multicompiler: equiv argc"      >: test_plugin "cbat-multicompiler-samples/equiv_argc" unsat;
  "Multicompiler: switch cases"    >: test_plugin "cbat-multicompiler-samples/switch_case_assignments" unsat;

  "Diff pointer val"               >: test_plugin "diff_pointer_val" sat;
  "Diff ret val"                   >: test_plugin "diff_ret_val" sat;

  "Double dereference"             >: test_plugin "double_dereference" unsat;

  "Equiv argc"                     >: (
    let models = [ [("RDI", "0x0000000000000002")]; ] in
    test_plugin "equiv_argc" sat
      ~reg_list:(lift_out_regs models) ~checker:(Some (check_list models))
  );

  "Precondition: force 2"          >: (
    let models = [ [("RDI", "0x0000000000000002")]; ] in
    test_plugin "equiv_argc" sat ~script:"run_wp_force.sh"
      ~reg_list:(lift_out_regs models) ~checker:(Some (check_list models)));

  "Precondition: disallow 2"       >: test_plugin "equiv_argc" unsat
    ~script:"run_wp_disallow.sh";

  "Equiv null check"               >: test_plugin "equiv_null_check" sat;

  "Function name map"             >: test_plugin "func_name_map" unsat;
  "Function name map with calls"  >:: test_skip fail_msg (test_plugin "func_name_map_calls" unsat);

  "Init var compare: UNSAT"        >: test_plugin "init_var_compare" unsat;
  "Init var compare: SAT"          >: test_plugin "init_var_compare" sat
    ~script:"run_wp_sat.sh";

  "Arrays in data section"         >: test_plugin "memory_samples/arrays" sat;
  "Arrays in data section"         >: test_plugin "memory_samples/arrays" sat
    ~script:"run_wp_mem_offset.sh";
  "Arrays in data section"         >: test_plugin "memory_samples/arrays" sat
    ~script:"run_wp_pre.sh";
  "Arrays in data section"         >: test_plugin "memory_samples/arrays" unsat
    ~script:"run_wp_pre_mem_offset.sh";
  "Arrays in data section"         >: test_plugin "memory_samples/arrays" unsat
    ~script:"run_wp_addr_rewrite.sh";

  "Data/BSS sections"              >: test_plugin "memory_samples/data_bss_sections" sat;
  "Data/BSS sections"              >: test_plugin "memory_samples/data_bss_sections" unsat
    ~script:"run_wp_mem_offset.sh";
  "Data/BSS sections"              >: test_plugin "memory_samples/data_bss_sections" unsat
    ~script:"run_wp_addr_rewrite.sh" ~length:Short;

  "Diff data section"              >:: test_skip fail_msg (test_plugin "memory_samples/diff_data" sat);

  "Same data, diff location"       >: test_plugin "memory_samples/diff_data_location" sat;
  "Same data, diff location"       >: test_plugin "memory_samples/diff_data_location" unsat
    ~script:"run_wp_mem_offset.sh";
  "Same data, diff location"       >: test_plugin "memory_samples/diff_data_location" unsat
    ~script:"run_wp_addr_rewrite.sh";

  "Diff stack values"              >: test_plugin "memory_samples/diff_stack" sat;

  "Memory hooks"                   >: test_plugin "memory_samples/mem_hooks" sat;

  "Name matching"                  >: test_plugin "memory_samples/name_matching" unsat;
  "Name matching"                  >: test_plugin "memory_samples/name_matching" unsat
    ~script:"run_wp_addr_rewrite.sh";

  "No position independent"        >: test_plugin "no_position_independent" sat;

  "No stack protection"            >: test_plugin "no_stack_protection" sat
    ~length:Short;

  "Null dereference: no check"     >: test_plugin "non_null_check" unsat;
  "Null dereference: with check"   >: test_plugin "non_null_check" sat
    ~script:"run_wp_null_deref.sh";

  "Pointer input"                  >: test_plugin "pointer_input" unsat;

  "Position independent"           >: test_plugin "position_independent" sat;

  "Retrowrite stub: pop RSP"       >: test_plugin "retrowrite_stub" unsat;
  "Retrowrite stub: inline AFL"    >: test_plugin "retrowrite_stub" unsat
    ~script:"run_wp_inline_afl.sh";
  "Retrowrite stub: inline all"    >: test_plugin "retrowrite_stub" unsat
    ~script:"run_wp_inline_all.sh";
  "Retrowrite stub no ret in call" >: test_plugin "retrowrite_stub_no_ret" unsat;

  "Same signs: post registers"     >: test_plugin "same_signs" unsat;
  "Same signs: postcondition"      >: test_plugin "same_signs" unsat
    ~script:"run_wp_postcond.sh";

  "Switch case assignments"        >: (
    let models = [ [("RDI", "0x0000000000000000")]; ] in
    test_plugin "switch_case_assignments" sat ~reg_list:(lift_out_regs models)
      ~checker:(Some (check_list models)));

  "Switch Cases"                   >: (
    let models = [ [("RDI", "0x0000000000000003")]; ] in
    test_plugin "switch_cases" sat ~reg_list:(lift_out_regs models)
      ~checker:(Some (check_list models)));

  "Switch Cases: Diff Ret Val"     >: (
    let models = [ [("RDI", "0x0000000000000003")]; ] in
    test_plugin "switch_cases_diff_ret" sat ~reg_list:(lift_out_regs models)
      ~checker:(Some (check_list models)));

  "Indirect call with return"      >: test_plugin "indirect_call_return" unsat;
  "Indirect call with no return"   >: test_plugin "indirect_call_no_return" unsat;

  "Test without pointer flag"      >: test_plugin "pointer_flag" sat ~script:"run_wp_sat.sh";
  "Test with pointer flag"         >: test_plugin "pointer_flag" unsat ~script:"run_wp_unsat.sh";

  "Loop unrolling comparative" >: test_plugin "loop/loop_depth_one" unsat ~script:"run_wp_compare.sh";

  "User defined sub specs comparative 1" >: test_plugin "user_func_spec/sub_spec_3"
    unsat ~script:"run_wp_comp.sh";  
  "User defined sub specs comparative 2" >: test_plugin "user_func_spec/sub_spec_4"
    unsat ~script:"run_wp_1.sh";
  
  (* Test single elf *)

  "Conditional call"               >: test_plugin "conditional_call" unsat;

  "Function call"                  >: (
    let models = [ [("RDI", "0x0000000000000005")]; ] in
    test_plugin "function_call" sat
      ~script:"run_wp_inline_foo.sh" ~reg_list:(lift_out_regs models)
      ~checker:(Some (check_list models))
  );
  "Function call: inline all"      >: (
    let models = [ [("RDI", "0x0000000000000005")]; ] in
    test_plugin "function_call" sat
      ~script:"run_wp_inline_all.sh" ~reg_list:(lift_out_regs models)
      ~checker:(Some (check_list models))
  );


  "Function spec: no inlining"     >: test_plugin "function_spec" sat;
  "Function spec: inline foo"      >: test_plugin "function_spec" unsat
    ~script:"run_wp_inline_foo.sh";
  "Function spec: inline all "     >: test_plugin "function_spec" unsat
    ~script:"run_wp_inline_all.sh";
  "Function spec: inline garbage"  >: test_plugin "function_spec" sat
    ~script:"run_wp_inline_garbage.sh";

  "Goto string"                    >: test_plugin "goto_string" sat;
  "Goto string: inline all"        >: test_plugin "goto_string" sat
    ~script:"run_wp_inline.sh";

  "Init var value in post: UNSAT:" >: test_plugin "init_var" unsat;
  "Init var value in post: SAT"    >: test_plugin "init_var" sat
    ~script:"run_wp_sat.sh";

  "Linked list: no mem check"      >: test_plugin "linked_list" unsat;
  "Linked list: with mem check"    >: test_plugin "linked_list" sat
    ~script:"run_wp_null_deref.sh";

  "Loop with assert"               >: test_plugin "loop/loop_with_assert" sat ~script:"run_wp.sh";

  "Loop full unroll"               >: (
    let models = [ [("RDI", "0x0000000000000005")]; ] in
    test_plugin "loop/loop_depth_one" sat ~script:"run_wp_single.sh"
      ~reg_list:(lift_out_regs models)
      ~checker:(Some (check_list models));
  );

  "Loop incomplete unroll"         >:: test_skip fail_msg
    (
      let models = [ [("RDI", "0x0000000000000005")]; ] in
      test_plugin "loop/loop_depth_one" sat ~script:"run_wp_less_loop.sh"
        ~reg_list:(lift_out_regs models)
        ~checker:(Some (check_list models))
    );

  "Loop incomplete unroll"         >:: test_skip fail_msg
    (test_plugin "loop/loop_depth_one" sat);

  "Nested function calls"               >: test_plugin "nested_function_calls" unsat;

  "Nested function calls: inline regex" >: (
    let models = [ [("RDI", "0x0000000000000004")]; ] in
    test_plugin "nested_function_calls" sat
      ~script:"run_wp_inline_regex.sh" ~reg_list:(lift_out_regs models)
      ~checker:(Some (check_list models))
  );

  "Nested function calls: inline all"   >: (
    let models = [ [("RDI", "0x0000000000000004")]; ] in
    test_plugin "nested_function_calls" sat
      ~script:"run_wp_inline_all.sh" ~reg_list:(lift_out_regs models)
      ~checker:(Some (check_list models))
  );


  "Nested ifs"                     >: test_plugin "nested_ifs" unsat;
  "Nested ifs: goto"               >: test_plugin "nested_ifs" unsat
    ~script:"run_wp_goto.sh";
  "Nested ifs: inline"             >: test_plugin "nested_ifs" unsat
    ~script:"run_wp_inline.sh";

  "Null dereference: no check"     >: test_plugin "null_deref" unsat;
  "Null dereference: with check"   >: test_plugin "null_deref" sat
    ~script:"run_wp_null_deref.sh";

  "Unconditional call"             >: test_plugin "unconditional_call" sat;

  "User defined postcondition"     >: test_plugin "return_argc" sat;

  "Simple WP"                      >: (
    let models = [[("RDI", "0x0000000000000003")]] in
    test_plugin "simple_wp" sat ~reg_list:(lift_out_regs models)
      ~checker:(Some (check_list models))
  );

  "Simple WP: precondition"        >: test_plugin "simple_wp" unsat
    ~script:"run_wp_pre.sh";

  "Single test without pointer flag" >: test_plugin "pointer_flag_single"
    sat ~script:"run_wp_sat.sh";
  "Single test with pointer flag"    >: test_plugin "pointer_flag_single"
    unsat ~script:"run_wp_unsat.sh";

  "Verifier assume SAT"            >: test_plugin "verifier_calls" sat
    ~script:"run_wp_assume_sat.sh";
  "Verifier assume UNSAT"          >: test_plugin "verifier_calls" unsat
    ~script:"run_wp_assume_unsat.sh";
  "Verifier nondent"               >: test_plugin "verifier_calls" sat
    ~script:"run_wp_nondet.sh";
  
  "User defined sub specs single 1" >: test_plugin "user_func_spec/sub_spec_1"
    unsat ~script:"run_wp_1.sh";
  "User defined sub specs single 2" >: test_plugin "user_func_spec/sub_spec_1"
    sat ~script:"run_wp_2.sh";
  "User defined sub specs single 3" >: test_plugin "user_func_spec/sub_spec_1"
    sat ~script:"run_wp_3.sh";
  "User defined sub specs single 4" >: test_plugin "user_func_spec/sub_spec_1"
    sat ~script:"run_wp_4.sh";
  "User defined sub specs single 5" >: test_plugin "user_func_spec/sub_spec_2"
    sat ~script:"run_wp_1.sh";
  "User defined sub specs single 6" >: test_plugin "user_func_spec/sub_spec_2"
    unsat ~script:"run_wp_2.sh";
  "User defined sub specs single 7" >: test_plugin "user_func_spec/sub_spec_3"
    unsat ~script:"run_wp_single_1.sh";
  "User defined sub specs single 8" >: test_plugin "user_func_spec/sub_spec_3"
    sat ~script:"run_wp_single_2.sh";
  "User defined sub specs single 9" >: test_plugin "user_func_spec/sub_spec_3"
    unsat ~script:"run_wp_single_3.sh";
  ]
