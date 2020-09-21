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
open Bap.Std
open OUnit2
open OUnitTest

module StringMap = Map.Make(String);;
module StringSet = Set.Make(String);;
module IntSet = Set.Make(Int);;


(* To run these tests: `make test` in wp directory *)

let bin_dir = "../resources/sample_binaries"

let timeout_msg = "Test times out!"

let fail_msg = "Test currently fails!"

let sat = "SAT!"

let unsat = "UNSAT!"

let unknown = "UNKNOWN!"

(* given a line of cbat output, checks
    that if the line specifies the result (sat or unsat),
    that it matches what is expected *)
let check_z3_result (line : string) (expected : string) (ctxt : test_ctxt) : unit =
  if List.exists [sat; unsat; unknown] ~f:(String.equal line) then
    assert_equal
      ~ctxt
      ~printer:String.to_string
      ~cmp:String.equal
      expected line
  else
    ()

(* given a line of cbat output and a register,
 * checks if that line contains the countermodel that includes reg *)
let try_reg (line : string) (reg : string) : (string * string) option =
  (* Our model is printed in the form "reg |-> value".
   *  This regex will break if this changes. *)
  let pattern = Format.sprintf "^\t+%s +|-> +#[a-z0-9]$" reg in
  let re = Re.Posix.compile_pat pattern in
  if Re.execp re line then
    begin
      let re = Re.Posix.compile_pat " +" in
      let tokens = Re.split re line in
      let actual = List.last_exn tokens in
      (* Value is stored in the last index. *)
      Some (reg, actual)
    end
  else None

(* given a line, checks if line contains the countermodel for a register *)
let get_reg_from_line (line : string) (regs_list : StringSet.t) :
  (* reg by model*)
  (string * string) option
  =
  StringSet.fold regs_list ~init:(None)
    ~f:(fun result reg ->
        match result with
        | Some _ -> result
        | None -> try_reg line reg
      )

(* Look for a line containing SAT!, UNSAT!, or UNKNOWN! in
   plugin output and compare with expected countermodel and result *)
let check_result (stream : char Stream.t) (expected_result : string)
    (regs_list : StringSet.t)
    (checker_wrapped: ((string StringMap.t) -> string option) option)
    (ctxt : test_ctxt) : unit =
  let buff = Buffer.create 16 in
  let results = StringMap.empty in
  (* TODO change this to a list *)
  let acc = ref results in
  Stream.iter (fun c ->
      match c with
      |'\n' ->
        let line = Buffer.contents buff in
        check_z3_result line expected_result ctxt;
        (* if the line has part of the model on it, put in map
         * otherwise do nothing since the line is irrelevant *)
        begin match get_reg_from_line line regs_list with
          | Some (reg_key, hex_val) ->
            let additional_results =
              StringMap.add_exn !acc ~key:reg_key ~data:hex_val in
            acc := additional_results; ()
          | None -> ()
        end ;
        Buffer.clear buff
      | chr ->
        Buffer.add_char buff chr)
    stream;
  match checker_wrapped with
  | Some checker ->
    begin match checker !acc with
      | None -> ()
      | Some err -> assert_failure err
    end
  | None -> ()


(*  given expected register models this function returns a function
 *  that determines whether or not one of the expected countermodels
 *   exactly matches the observed countermodel*)
let check_list (expected_reg_models : ((string * string) list) list )
  : (string StringMap.t -> string option) =
  fun observed_mapping ->
  List.foldi expected_reg_models ~init:(Some "") ~f:(fun i seen_match model ->
      match seen_match with
      | Some err ->
        let result = List.fold model ~init:(None) ~f:(fun acc (reg, value) ->
            let err =
              begin match StringMap.find observed_mapping reg with
                (* if register not observed, then fail *)
                | None ->
                  Printf.sprintf
                    "\n\tRegister %s not found in returned model.\n"
                    reg |> Some
                | Some observed_value ->
                  if observed_value = value then None
                  else
                    Printf.sprintf
                      "\tRegister mismatch: %s expected to be %s but was %s\n"
                      reg value observed_value |> Some
              end in
            Option.merge ~f:(^) acc err
          ) in
        begin match result with
          | None -> None
          | Some cur_err ->
            let model_msg = (Printf.sprintf "\nModel %d:\n" i) in
            err ^ model_msg ^ cur_err |> Some
        end
      | None -> seen_match
    )

(* given a list of registers, [register_names], and a mapping
 * from registers to bitvector values, returns a list of bitvectors
 *  corresponding to those registers in [register_name]. Preserves order *)
let gather_register_values (register_names : string list) (mapping: string StringMap.t)
  : Bitvector.t list =
  register_names |> List.map ~f:(fun name ->
      (* we want an exception if the register name is not found *)
      StringMap.find_exn mapping name |> int_of_string |> Bitvector.of_int ~width:64
    )

(* given a list of bitvectors representing a game board, [board_list],
 *  and a size of an entry in the game board [mask_width],
 *  returns the element seen at index [index] in the board. *)
let get_element (board_list : Bitvector.t list) (mask_width : int) (index : int): int =
  let width = 64 in
  let mask = List.range ~stride:1 ~start:`inclusive ~stop:`exclusive 0 mask_width
             |> List.fold ~init:(0) ~f:(fun acc i -> acc + (1 lsl i))
             |> Bitvector.of_int ~width:width in
  let bits_to_shift = index * mask_width in
  let shift_distance_int = (bits_to_shift) / width in
  let board = List.nth_exn board_list shift_distance_int in
  let shift_distance =  bits_to_shift mod width |> Bitvector.of_int ~width:width in
  let shifted_mask = Bitvector.lshift mask shift_distance in
  let masked_board = Bitvector.logand shifted_mask board in
  Bitvector.rshift masked_board shift_distance |> Bitvector.to_int_exn

(* given an [n] by [n] board represented as a list of bitvectors,
 *  checks if board satisfies nqueen constraints on
 *  columns, rows, and diagonals. *)
let check_n_queen_diag_col_row (n : int) (board: Bitvector.t list): string option =
  let ge = get_element board 1 in
  let indxs = List.range ~stride:1 ~start:`inclusive ~stop:`exclusive 0 n in
  let has_exactly_one_queen = List.fold indxs ~init:(None) ~f:(fun acc i ->
      let l = List.fold indxs ~init:(List.init 6 ~f:(fun _ -> 0))
          ~f:(fun acc_inner j ->
              let first = [
                (* row *)
                j + i * n |> ge;
                (* column *)
                j * n + i |> ge;
              ] in
              let second =
                if j < n - i then
                  (* diags *)
                  [
                    i + (n + 1) * j |> ge;
                    n * i + (n + 1) * j |> ge;
                    n * i + (n - 1) * (j + 1) |> ge;
                    (n - 1) + j * (n - 1) - i |> ge;
                  ]
                else List.init 4 ~f:(fun _ -> 0)
              in
              let result = List.append first second in
              List.zip_exn acc_inner result |> List.map ~f:(fun (l, r) -> l + r)) in
      let gen_err = fun i v t ->
        (* first condition is on requiring exactly one queen in a column or row *)
        (* second condition is requiring at most one queen in a diagonal  *)
        if (v = 1 && i < 2) || (v <= 1 && 2 <= i) then None
        else Printf.sprintf "\n%s %d incorrect\n" t i |> Some in
      let err_types = ["row"; "col"; "right diagonal lower";
                       "right diagonal upper"; "left diagonal lower";
                       "left diagonal upper"] in
      List.zip_exn l err_types |> List.mapi ~f:(fun i (v, t) -> gen_err i v t)
      |> List.fold ~init:(None) ~f:(fun acc_inner v -> Option.merge acc_inner v ~f:(^))
      |>  Option.merge acc ~f:(^)
    ) in
  has_exactly_one_queen

(* Obtains the list registers in the x86-64 specified by the sysV AMD64 ABI, *)
let get_register_args (n : int) (arch : Arch.t): string list =
  List.slice (Bap_wp.Precondition.input_regs arch) 0 n
  |> List.map ~f:(fun x -> Var.to_string x |> String.uppercase)

(* returns a function that checks a [n] by [n] nqueens board. *)
let check_n_queens (n: int) (arch : Arch.t) : (string StringMap.t -> string option) =
  fun var_mapping ->
  let width = 64 in
  let board_args = get_register_args 4 arch in
  let num_bits = n * n in
  let num_registers = num_bits / width in
  (* make sure we can feasibly handle the input.
      Chokes at 16 x 16 which fits in 4 64 bit registers *)
  if num_registers > 4 then assert_failure
      "N QUEENS example run on too large of an n";
  (* n <= 3 has no solutions *)
  if n <= 3 then assert_failure "Nqueens example run on too small of an n";
  let filtered_board_args = board_args |> List.filteri ~f:(fun i _ -> i >= num_registers)
  in
  let board_pieces = gather_register_values filtered_board_args var_mapping in
  check_n_queen_diag_col_row n board_pieces

(* given a sudoku board and list of indices,
   check that indices preserve sudoku invariants *)
let check_sudoku_conditions (indices : int list) (board : Bitvector.t) : string option =
  let mask_size = 2 in
  let expected_values = List.range 0 4 |> IntSet.of_list in
  let actual_values =
    List.map indices ~f:(fun x -> get_element [board] mask_size x) |> IntSet.of_list in
  if
    (IntSet.inter expected_values actual_values |> IntSet.length)
    = (IntSet.length expected_values)
  then None else
    let indx_str =
      List.fold indices ~init:("") ~f:(fun acc x -> acc ^ "," ^ (string_of_int x)) in
    Printf.sprintf "\n indices %s did not match what was expected" indx_str |> Some

(* check a 2 by 2 sudoku game *)
let check_two_by_two_sudoku (var_mapping : string StringMap.t) : string option =
  let sudoku_board = gather_register_values ["RDI";] var_mapping |> List.hd_exn in
  let snippets =
    [[0; 1; 2; 3]; [4; 5; 6; 7]; [8; 9; 10; 11]; [12; 13; 14; 15];
     [0; 4; 8; 12]; [1; 5; 9; 13]; [2; 6; 10; 14]; [3; 7; 11; 15];
     [0; 1; 4; 5]; [2; 3; 6; 7;]; [8; 9; 12; 13]; [10; 11; 14; 15];] in
  List.fold snippets ~init:(None)
    ~f:(fun acc l -> Option.merge acc (check_sudoku_conditions l sudoku_board) ~f:(^))

(* perform the bad hash given a current hash and register input *)
let bad_hash_function (c : Bitvector.t) (cur_hash : Bitvector.t) (reg_size : int) =
  let first_num, second_num, third_num = 0x6, 0x10, 0x20 in
  let t_1 = Bitvector.lshift cur_hash (Bitvector.of_int first_num ~width:reg_size) in
  let t_2 = Bitvector.lshift cur_hash (Bitvector.of_int second_num ~width:reg_size) in
  let t_3 = Bitvector.add c t_1 |> Bitvector.add t_2 in
  let result = Bitvector.sub t_3 cur_hash in
  Bitvector.modulo result (Bitvector.of_int third_num ~width:reg_size)

(* check the bad hash function *)
let check_bad_hash_function (registers : string list) : ((string StringMap.t) -> string option) =
  let reg_size = 32 in
  fun var_mapping ->
    (* index of the special character *)
    let result_index = Bitvector.of_int 0xf ~width:reg_size in
    let result = gather_register_values registers var_mapping
                 |> List.fold ~init:(Bitvector.of_int 0x0 ~width:reg_size)
                   ~f:(fun acc v -> bad_hash_function v acc reg_size) in
    if result = result_index then
      None
    else
      Printf.sprintf "\n Expected the hash %s but got hash %s"
        (Bitvector.to_string result) (Bitvector.to_string result_index)
      |> Some

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
    ?reg_list:(reg_list = StringSet.empty)
    ?checker:(checker = None)
    (elf_dir : string)
    (expected_result : string)
  : test =
  let target = Format.sprintf "%s/%s" bin_dir elf_dir in
  let script = Format.sprintf "./%s" script in
  let test ctxt =
    assert_command script []
      ~foutput:(fun res -> check_result res expected_result reg_list checker ctxt)
      ~backtrace:true
      ~chdir:target
      ~ctxt:ctxt
  in
  test_case ~length test

let test_skip (msg : string) (_ : test) (_ : test_ctxt) : unit =
  skip_if true msg

(* given a list of lists of models, where each
 * element of a model has the form (reg, value),
 *  returns the set of registers contained in the model *)
let lift_out_regs (reg_value : ((string * string) list) list) : StringSet.t =
  List.fold reg_value ~init:(StringSet.empty) ~f:(fun acc model ->
      List.fold model ~init:(StringSet.empty) ~f:(fun acc (reg, _) ->
          StringSet.add acc reg) |> StringSet.union acc)

let suite = [

  "Equiv argc"                     >: (
    let models = [ [("RDI", "0x0000000000000002")]; ] in
    test_plugin "equiv_argc" sat
      ~reg_list:(lift_out_regs models) ~checker:(check_list models |> Some)
  );

  (* Test elf comparison *)

  "Multicompiler: csmith"          >: test_plugin "cbat-multicompiler-samples/csmith" unsat;
  "Multicompiler: csmith inline"   >:: test_skip timeout_msg (test_plugin "cbat-multicompiler-samples/csmith" unsat
                                                                ~script:"run_wp_inline.sh");
  "Multicompiler: equiv argc"      >: test_plugin "cbat-multicompiler-samples/equiv_argc" unsat;
  "Multicompiler: switch cases"    >: test_plugin "cbat-multicompiler-samples/switch_case_assignments" unsat;

  "Diff pointer val"               >: test_plugin "diff_pointer_val" sat;
  "Diff ret val"                   >: test_plugin "diff_ret_val" sat;

  "Double dereference"             >: test_plugin "double_dereference" unsat;

  "Precondition: force 2"          >: (
    let models = [ [("RDI", "0x0000000000000002")]; ] in
    test_plugin "equiv_argc" sat ~script:"run_wp_force.sh"
      ~reg_list:(lift_out_regs models) ~checker:(check_list models |> Some));

  "Precondition: disallow 2"       >: test_plugin "equiv_argc" unsat
    ~script:"run_wp_disallow.sh";

  "Equiv null check"               >: test_plugin "equiv_null_check" sat;

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

  "ROP example"                    >:: test_skip fail_msg (test_plugin "rop_example" unsat);

  "Same signs: post registers"     >: test_plugin "same_signs" unsat;
  "Same signs: postcondition"      >: test_plugin "same_signs" unsat
    ~script:"run_wp_postcond.sh";

  "Switch case assignments"        >: (
    let models = [ [("RDI", "0x0000000000000000")]; ] in
    test_plugin "switch_case_assignments" sat ~reg_list:(lift_out_regs models)
      ~checker:(check_list models |> Some));

  "Switch Cases"                   >: (
    let models = [ [("RDI", "0x0000000000000003")]; ] in
    test_plugin "switch_cases" sat ~reg_list:(lift_out_regs models)
      ~checker:(check_list models |> Some));

  "Switch Cases: Diff Ret Val"     >: (
    let models = [ [("RDI", "0x0000000000000003")]; ] in
    test_plugin "switch_cases_diff_ret" sat ~reg_list:(lift_out_regs models)
      ~checker:(check_list models |> Some));

  "Indirect call with return"      >: test_plugin "indirect_call_return" unsat;
  "Indirect call with no return"   >: test_plugin "indirect_call_no_return" unsat;

  (* Test single elf *)

  "Function call"                  >: (
    let models = [ [("RDI", "0x0000000000000005")]; ] in
    test_plugin "function_call" sat
      ~script:"run_wp_inline_foo.sh" ~reg_list:(lift_out_regs models)
      ~checker:(check_list models |> Some)
  );
  "Function call: inline all"      >: (
    let models = [ [("RDI", "0x0000000000000005")]; ] in
    test_plugin "function_call" sat
      ~script:"run_wp_inline_all.sh" ~reg_list:(lift_out_regs models)
      ~checker:(check_list models |> Some)
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

  "Loop"                           >: test_plugin "loop" sat;

  "Nested function calls"               >: test_plugin "nested_function_calls" unsat;
  "Nested function calls: inline regex" >: (
    let models = [ [("RDI", "0x0000000000000004")]; ] in
    test_plugin "nested_function_calls" sat
      ~script:"run_wp_inline_regex.sh" ~reg_list:(lift_out_regs models)
      ~checker:(check_list models |> Some)
  );

  "Nested function calls: inline all"   >: (
    let models = [ [("RDI", "0x0000000000000004")]; ] in
    test_plugin "nested_function_calls" sat
      ~script:"run_wp_inline_all.sh" ~reg_list:(lift_out_regs models)
      ~checker:(check_list models |> Some)
  );


  "Nested ifs"                     >: test_plugin "nested_ifs" unsat;
  "Nested ifs: goto"               >: test_plugin "nested_ifs" unsat
    ~script:"run_wp_goto.sh";
  "Nested ifs: inline"             >: test_plugin "nested_ifs" unsat
    ~script:"run_wp_inline.sh";

  "Null dereference: no check"     >: test_plugin "null_deref" unsat;
  "Null dereference: with check"   >: test_plugin "null_deref" sat
    ~script:"run_wp_null_deref.sh";

  "User defined postcondition"     >: test_plugin "return_argc" sat;

  "Simple WP"                      >: (
    let models = [[("RDI", "0x0000000000000003")]] in
    test_plugin "simple_wp" sat ~reg_list:(lift_out_regs models)
      ~checker:(check_list models |> Some)
  );

  "Simple WP: precondition"        >: test_plugin "simple_wp" unsat
    ~script:"run_wp_pre.sh";

  "Verifier assume SAT"            >: test_plugin "verifier_calls" sat
    ~script:"run_wp_assume_sat.sh";
  "Verifier assume UNSAT"          >: test_plugin "verifier_calls" unsat
    ~script:"run_wp_assume_unsat.sh";
  "Verifier nondent"               >: test_plugin "verifier_calls" sat
    ~script:"run_wp_nondet.sh";

  (* Test performance *)

  "Debruijn: 8 bit"                >: test_plugin "debruijn" unsat
    ~script:"run_wp_8bit.sh";
  "Debruijn: 16 bit"               >: test_plugin "debruijn" unsat
    ~script:"run_wp_16bit.sh";
  "Debruijn: 32 bit"               >: test_plugin "debruijn" unsat
    ~script:"run_wp_32bit.sh";

  "NQueens solver 4x4"             >: (
    test_plugin "nqueens" sat
      ~reg_list:(["RDI"; "RSI"; "RDX"; "RCX"] |> StringSet.of_list)
      ~checker:(check_n_queens 4 `x86_64 |> Some)
  );


  "Sudoku solver"                  >: (
    test_plugin "sudoku" sat ~reg_list:(["RDI"] |> StringSet.of_list)
      ~checker:(check_two_by_two_sudoku |> Some)
  );


  "Hash function"                  >: (
    let registers =  get_register_args 5 `x86_64 in
    test_plugin "hash_function" sat
      ~reg_list:(registers |> StringSet.of_list)
      ~checker:(check_bad_hash_function registers |> Some)
  );


]
