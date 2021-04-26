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

module Pre = Bap_wp.Precondition
module Utils = Bap_wp.Utils

(* To run these tests: `make test` in wp directory *)

let test_update_num_unroll
    ?length:(length = Immediate)
    (new_unroll : int option)
  : test =
  let original = !Pre.num_unroll in
  Utils.update_default_num_unroll new_unroll;
  let updated = !Pre.num_unroll in
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

let suite = [

  "Update Number of Unrolls"       >: test_update_num_unroll (Some 3);
  "Original Number of Unrolls"     >: test_update_num_unroll None;

]
