open OUnitTest
open Test_lib.Test_wp_utils

let integration_tests = List.append [

    (* Test performance *)

    "Debruijn: 8 bit"                >: test_plugin "debruijn" unsat
      ~script:"run_wp_8bit.sh";
    "Debruijn: 16 bit"               >: test_plugin "debruijn" unsat
      ~script:"run_wp_16bit.sh";
    "Debruijn: 32 bit"               >: test_plugin "debruijn" unsat
      ~script:"run_wp_32bit.sh";
    "Debruijn: 32 bit Boolector"     >: test_plugin "debruijn" unsat
      ~script:"run_wp_32bit_boolector.sh";

    "Sudoku solver 2x2"                  >: (
      test_plugin "sudoku_2_by_2" sat ~reg_list:(["RDI"] |> StringSet.of_list)
        ~checker:(Some check_two_by_two_sudoku ));

    "Sudoku solver 2x2 Boolector"        >: (
      test_plugin "sudoku_2_by_2" sat ~reg_list:(["RDI"] |> StringSet.of_list)
        ~checker:(Some check_two_by_two_sudoku)
        ~script:"run_wp_boolector.sh");

    "Sudoku solver 3x3"                  >:: (test_skip timeout_msg (
        let models = [[("RDI", "0x3867501865103742"); ("RSI", "0x1285070152436824");
                       ("RDX", "0x4765867402134376"); ("RCX", "0x4620435187012358");
                       ("R8", "0x7408162515827603"); ("R9", "0x0000000000000003")]] in
        test_plugin "sudoku_3_by_3" sat ~reg_list:(["RDI"] |> StringSet.of_list)
          ~checker:(Some (check_list models))));

    "Hash function"                  >: (
      let registers =  get_register_args 5 X86_target.amd64 in
      test_plugin "hash_function" sat
        ~reg_list:(registers |> StringSet.of_list)
        ~checker:(Some (check_bad_hash_function registers)));
  ] nqueens_tests
