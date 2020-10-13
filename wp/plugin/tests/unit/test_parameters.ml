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
open OUnitTest
open !Core_kernel
open Bap_main

module Params = Parameters

(* To run these tests: `make test` in wp directory *)

let test_validate_input
    ?length:(length = Immediate)
    ~valid:(valid : bool)
    (res : (unit, error) result)
   : test =
  let test _ = match res with
    | Error _ -> assert_bool "Returned an error when params are valid" (not valid)
    | Ok () -> assert_bool "Should have returned an error for an invalid param" valid
  in
  test_case ~length test

let suite = [

  "No function specified" >: test_validate_input ~valid:false
    (Params.validate_func "");
  "Function specified" >: test_validate_input ~valid:true
    (Params.validate_func "main");

  "Invalid option for debug" >: test_validate_input ~valid:false
    (Params.validate_debug ["foo"]);
  "Valid option for debug" >: test_validate_input ~valid:true
    (Params.validate_debug ["z3-solver-stats"]);

  "Invalid option for show" >: test_validate_input ~valid:false
    (Params.validate_show ["foo"]);
  "Valid option for debug" >: test_validate_input ~valid:true
    (Params.validate_show ["bir"]);

  "One file for compare_func_calls" >: test_validate_input ~valid:false
    (Params.validate_compare_func_calls true ["exe1"]);
  "Two files for compare_func_calls" >: test_validate_input ~valid:true
    (Params.validate_compare_func_calls true ["exe1"; "exe2"]);

  "One file for compare_post_reg_values" >: test_validate_input ~valid:false
    (Params.validate_compare_post_reg_vals ["x"] ["exe1"]);
  "Two files for compare_post_reg_values" >: test_validate_input ~valid:true
    (Params.validate_compare_post_reg_vals ["x"] ["exe1"; "exe2"]);

]
