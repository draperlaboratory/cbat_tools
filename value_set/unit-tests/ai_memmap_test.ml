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

include Bap.Std
open Test_utils
open OUnit2
module Mem = Cbat_ai_memmap
(* TODO: functorize/rename *)
module Clp = Cbat_clp_set_composite

module Option = Core_kernel.Option

let mem_key = {Mem.addr_width=64;Mem.addressable_width=8}

let test_defaults _ =
  List.iter begin fun p ->
    let p = Clp.of_clp p in
    Option.iter (Mem.Key.of_wordset p) ~f:begin fun addr ->
      let tempty = Mem.top mem_key in
      let bempty = Mem.bottom mem_key in
      let tval = Mem.find (64, LittleEndian) tempty addr in
      let bval = Mem.find (64, LittleEndian) bempty addr in
      assert_bool "find of top returns top" (Mem.Val.is_top tval);
      assert_bool "find of bottom returns bottom" (Mem.Val.is_bottom bval)
    end
  end test_clps_64


let test_add _ =
  let tempty = Mem.top mem_key in
  let bempty = Mem.bottom mem_key in
  let le64 = 64, LittleEndian in
  List.iter begin fun p1 ->
    let p1 = Clp.of_clp p1 in
    List.iter begin fun p2 ->
      let p2 = Clp.of_clp p2 in
      Option.iter (Mem.Key.of_wordset p1) ~f:begin fun addr ->
        let p2 = Mem.Val.create p2 LittleEndian in
        let top_add_adder = Mem.add tempty ~key:addr ~data:p2 in
        let bot_add_adder = Mem.add bempty ~key:addr ~data:p2 in
        let top_jadd_adder = Mem.join_add tempty ~key:addr ~data:p2 in
        let bot_jadd_adder = Mem.join_add bempty ~key:addr ~data:p2 in
        let top_madd_adder = Mem.meet_add tempty ~key:addr ~data:p2 in
        let bot_madd_adder = Mem.meet_add bempty ~key:addr ~data:p2 in
        let top_add_find = Mem.find le64 top_add_adder addr in
        let bot_add_find = Mem.find le64 bot_add_adder addr in
        let top_jadd_find = Mem.find le64 top_jadd_adder addr in
        let bot_jadd_find = Mem.find le64 bot_jadd_adder addr in
        let top_madd_find = Mem.find le64 top_madd_adder addr in
        Format.fprintf test_ppf "%a <= %a\n"
                 Clp.pp (Mem.Val.data p2)
                 Clp.pp (Mem.Val.data top_add_find);
        assert_bool "add-find approximates the input"
          (Mem.Val.precedes p2 top_add_find);
        Format.fprintf test_ppf "%a = %a\n"
                 Clp.pp (Mem.Val.data p2)
                 Clp.pp (Mem.Val.data bot_add_find);
        assert_bool "add with bottom produces bottom"
          (Mem.Val.equal bot_add_find (Mem.Val.bottom le64));
        Format.fprintf test_ppf "top <= %a\n"
                 Clp.pp (Mem.Val.data top_jadd_find);
        assert_bool "join_add to cell containing top stores top"
          (Clp.is_top @@ Mem.Val.data top_jadd_find);
        Format.fprintf test_ppf "%a <= %a\n"
                 Clp.pp (Mem.Val.data bot_jadd_find)
                 Clp.pp (Mem.Val.data p2);
        assert_bool "join_add with bottom produces bottom"
          (Mem.Val.equal bot_jadd_find (Mem.Val.bottom le64));
        print (Core_kernel.Sexp.to_string_hum
                 (Mem.sexp_of_t top_madd_adder));
        Format.fprintf test_ppf "%a <= %a\n"
                 Clp.pp (Mem.Val.data top_madd_find)
                 Clp.pp (Mem.Val.data p2);
        assert_bool "meet_add to top precedes input"
          (Mem.Val.precedes top_madd_find p2);
        assert_bool "meet_add to bottom stores bottom"
          (Mem.Val.is_bottom (Mem.find le64 bot_madd_adder addr));
      end
    end test_clps_64
  end test_clps_64


let all_tests =
 "abstract interpretation memory tests">:::[
   "memory defaults">::test_defaults;
   "add-find">::test_add;
 ]
