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

module Pre = Bap_wp.Precondition
module Utils = Bap_wp.Utils

(* To run these tests: `make test` in wp directory *)

let test_get_mod_func_name
    (re : (string * string) list)
    (name_orig : string)
    (expected : string option)
    (ctxt : test_ctxt)
  : unit =
  let cmp x y =
    match x, y with
    | Some x, Some y -> String.equal x y
    | None, None -> true
    | Some _, None | None, Some _ -> false
  in
  let result = Utils.get_mod_func_name re name_orig in
  assert_equal ~ctxt ~cmp expected result

let test_match_inline (_ : test_ctxt) : unit =
  let foo = Sub.create ~name:"foo" () in
  let bar = Sub.create ~name:"bar" () in
  let subs = Seq.of_list [foo; bar] in
  let result = Utils.match_inline (Some "foo") subs in
  let fail_msg = "match_inline could not find the subroutine to inline%!" in
  assert_bool fail_msg (Seq.exists result ~f:(Sub.equal foo))

let suite = [

  "test_get_mod_func_name" >:: test_get_mod_func_name [("\\(.*\\)", "\\1_mod")]
    "foo" (Some "foo_mod");
  "test_match_inline"      >:: test_match_inline

]
