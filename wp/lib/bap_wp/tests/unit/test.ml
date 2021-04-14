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

open OUnit2

let suite =
  "Unit Tests" >::: [
    "Precondition" >::: Test_precondition.suite;
    "Compare"      >::: Test_compare.suite;
    "Constraint"   >::: Test_constraint.suite;
    "Output"       >::: Test_output.suite;
    "Z3 Utils"     >::: Test_z3_utils.suite;
  ]

let _ =
  (* match Bap_main.init () with
   * | Ok () ->
   *   run_test_tt_main suite
   * | Error e ->
   *   let msg =
   *     Format.asprintf "Bap_main.init failed with error %a"
   *       Bap_main.Extension.Error.pp e
   *   in
   *   failwith msg *)
  run_test_tt_main suite
