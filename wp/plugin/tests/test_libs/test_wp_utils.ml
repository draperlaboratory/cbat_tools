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

open !Core
open Bap.Std
open Bap_core_theory
open OUnit2
open OUnitTest

module StringMap = Map.Make(String)
module StringSet = Set.Make(String)
module IntSet = Set.Make(Int)


(* To run these tests: `make test` or `make test.integration` in wp directory *)

let bin_dir = "../../../../../resources/sample_binaries"

let timeout_msg = "Test times out!"

let fail_msg = "Test currently fails!"

let sat = 1

let unsat = 0

let unknown = 2

(* given a line of cbat output and a register,
   checks if that line contains the countermodel that includes reg *)
let try_reg (line : string) (reg : string) : (string * string) option =
  (* Our model is printed in the form "reg |-> value".
     This regex will break if this changes. *)
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
        | None -> try_reg line reg)

let iter_stream (stream : char Stdlib.Seq.t) ~(f : char -> unit) : unit =
  try Stdlib.Seq.iter f stream with End_of_file -> ()

(* Look for a line containing specific outputs and compare with expected
   countermodel and result *)
let check_result (stream : char Stdlib.Seq.t)
    (regs_list : StringSet.t)
    (checker_wrapped: ((string StringMap.t) -> string option) option)
  : unit =
  let buff = Buffer.create 16 in
  let results = StringMap.empty in
  let acc = ref results in
  iter_stream stream ~f:(function
      |'\n' ->
        let line = Buffer.contents buff in
        (* if the line has part of the model on it, put in map
           otherwise do nothing since the line is irrelevant *)
        begin match get_reg_from_line line regs_list with
          | Some (reg_key, hex_val) ->
            let additional_results =
              StringMap.add_exn !acc ~key:reg_key ~data:hex_val in
            acc := additional_results
          | None -> ()
        end;
        Buffer.clear buff
      | chr -> Buffer.add_char buff chr);
  Option.iter checker_wrapped ~f:(fun checker ->
      checker !acc |> Option.iter ~f:assert_failure)

(*  given expected register models this function returns a function
    that determines whether or not one of the expected countermodels
    exactly matches the observed countermodel *)
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
                  Some (Printf.sprintf
                          "\n\tRegister %s not found in returned model.\n" reg)
                | Some observed_value ->
                  if String.equal observed_value value then None
                  else
                    Some (Printf.sprintf
                            "\tRegister mismatch: %s expected to be %s but was %s\n"
                            reg value observed_value)
              end in
            Option.merge ~f:(^) acc err
          ) in
        begin match result with
          | None -> None
          | Some cur_err ->
            let model_msg = (Printf.sprintf "\nModel %d:\n" i) in
            Some (err ^ model_msg ^ cur_err)
        end
      | None -> seen_match
    )

(* given a list of registers, [register_names], and a mapping, [mapping],
   from registers to bitvector values, returns a list of bitvectors
    corresponding to those registers in [register_name]. Preserves order *)
let gather_register_values (register_names : string list) (mapping: string StringMap.t)
  : Bitvector.t list =
  register_names |> List.map ~f:(fun name ->
      (* we want an exception if the register name is not found *)
      (StringMap.find_exn mapping name) ^ ":64u" |> Bitvector.of_string
    )

(* given a list of bitvectors [board_list] representing a game board, [board_list],
    and a size of an entry in the game board [mask_width],
    returns the element seen at index [index] in the board. *)
let get_element (board_list : Bitvector.t list) (mask_width : int) (index : int): int =
  let width = 64 in
  let mask = List.range 0 mask_width
             |> List.fold ~init:(0) ~f:(fun acc i -> acc + (1 lsl i))
             |> Bitvector.of_int ~width:width in
  let bits_to_shift = index * mask_width in
  let shift_distance_int = bits_to_shift / width in
  let board = List.nth_exn board_list shift_distance_int in
  let shift_distance =  bits_to_shift - (shift_distance_int * width)
                        |> Bitvector.of_int ~width:width in
  let shifted_mask = Bitvector.lshift mask shift_distance in
  let masked_board = Bitvector.logand shifted_mask board in
  Bitvector.rshift masked_board shift_distance |> Bitvector.to_int_exn

(* given an [n] by [n] board represented as a list of bitvectors [board_list],
    checks if board satisfies nqueen constraints on
    columns, rows, and diagonals. *)
let check_n_queen_diag_col_row (n : int) (board_list: Bitvector.t list): string option =
  let width = 1 in
  let ge = get_element board_list width in
  let num_constraints = 6 in
  let indxs = List.range 0 n in
  let has_exactly_one_queen = List.fold indxs ~init:(None) ~f:(fun acc i ->
      let l = List.fold indxs ~init:(List.init num_constraints ~f:(fun _ -> 0))
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
              List.zip_exn acc_inner result |> List.map ~f:(fun (a, b) -> a + b)) in
      let gen_err = fun err_idx v err_type ->
        (* first condition is on requiring exactly one queen in a column or row *)
        (* second condition is requiring at most one queen in a diagonal  *)
        if (v = 1 && err_idx < 2) || (v <= 1 && 2 <= err_idx) then None
        else Some (Printf.sprintf "\n%s %d incorrect. Got %d\n" err_type err_idx v) in
      let err_types = ["row"; "col"; "right diagonal lower";
                       "right diagonal upper"; "left diagonal lower";
                       "left diagonal upper"] in
      List.zip_exn l err_types |> List.mapi ~f:(fun err_idx (v, err_type) -> gen_err err_idx v err_type)
      |> List.fold ~init:(None)
        ~f:(fun acc_inner v -> Option.merge acc_inner v ~f:(^))
      |>  Option.merge acc ~f:(^)
    ) in
  has_exactly_one_queen

(* Obtains the list registers in the x86-64 specified by the sysV AMD64 ABI, *)
let get_register_args (n : int) (arch : Theory.target): string list =
  List.slice (Bap_wp.Precondition.input_regs arch) 0 n
  |> List.map ~f:(fun x -> Var.to_string x |> String.uppercase)

(* returns a function that checks a [n] by [n] nqueens board. *)
let check_n_queens (n: int) (arch : Theory.target) : (string StringMap.t -> string option) =
  fun var_mapping ->
  let width = 64 in
  let board_args = get_register_args 6 arch in
  let num_bits = n * n in
  let num_registers = num_bits / width in
  (* n <= 3 has no solutions *)
  if n <= 3 then assert_failure "Nqueens example run on too small of an n";
  let filtered_board_args = board_args |> List.filteri ~f:(fun i _ -> i <= num_registers)
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
    Some (Printf.sprintf "\n indices %s did not match what was expected" indx_str)

(* check a 2 by 2 sudoku game *)
let check_two_by_two_sudoku (var_mapping : string StringMap.t) : string option =
  let sudoku_board = gather_register_values ["RDI";] var_mapping |> List.hd_exn in
  let snippets =
    [[0; 1; 2; 3]; [4; 5; 6; 7]; [8; 9; 10; 11]; [12; 13; 14; 15];
     [0; 4; 8; 12]; [1; 5; 9; 13]; [2; 6; 10; 14]; [3; 7; 11; 15];
     [0; 1; 4; 5]; [2; 3; 6; 7;]; [8; 9; 12; 13]; [10; 11; 14; 15];] in
  List.fold snippets ~init:(None)
    ~f:(fun acc l -> Option.merge acc (check_sudoku_conditions l sudoku_board) ~f:(^))

(* perform the bad hash given a current hash and a register input *)
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
    if Bitvector.equal result result_index then
      None
    else
      Some (Printf.sprintf "\n Expected the hash %s but got hash %s"
              (Bitvector.to_string result) (Bitvector.to_string result_index))

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
    ?args:(args = [])
    ?reg_list:(reg_list = StringSet.empty)
    ?checker:(checker = None)
    (elf_dir : string)
    (expected_exit_code : int)
  : test =
  let target = Format.sprintf "%s/%s" bin_dir elf_dir in
  let script = Format.sprintf "./%s" script in
  let process_status = UnixLabels.WEXITED expected_exit_code in
  let test ctxt =
    assert_command script args
      ~exit_code:process_status
      ~foutput:(fun res -> check_result res reg_list checker)
      ~backtrace:true
      ~chdir:target
      ~ctxt:ctxt
  in
  test_case ~length test

let test_skip (msg : string) (_ : test) (_ : test_ctxt) : unit =
  skip_if true msg

(* given a list of lists of models, where each
   element of a model has the form (reg, value),
   returns the set of registers contained in the model *)
let lift_out_regs (reg_value : ((string * string) list) list) : StringSet.t =
  List.fold reg_value ~init:(StringSet.empty) ~f:(fun acc model ->
      List.fold model ~init:(StringSet.empty) ~f:(fun acc (reg, _) ->
          StringSet.add acc reg) |> StringSet.union acc)

let nqueens_tests = List.range 4 20 |> List.map ~f:(fun i ->
    let x86_64 = X86_target.amd64 in
    let description = Printf.sprintf "NQueens solver %dx%d" i i in
    let script = Printf.sprintf "run_wp.sh" in
    let test = (description >: test_plugin "nqueens" sat
                  ~reg_list:(get_register_args 6 x86_64 |> StringSet.of_list)
                  ~checker:(Some (check_n_queens i x86_64))
                  ~script:script ~args:[string_of_int i])
    in
    (* tests 17 to 19 currently time out *)
    if i > 16 then (description >:: (test_skip timeout_msg test)) else test)
