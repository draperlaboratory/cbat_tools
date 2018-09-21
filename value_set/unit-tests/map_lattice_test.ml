(***************************************************************************)
(*                                                                         *)
(*  Copyright (C) 2018 The Charles Stark Draper Laboratory, Inc.           *)
(*                                                                         *)
(*  This file is provided under the license found in the LICENSE file in   *)
(*  the top-level directory of this project.                               *)
(*                                                                         *)
(*  This work is funded in part by ONR/NAWC Contract N6833518C0107.  Its   *)
(*  content does not necessarily reflect the position or policy of the US  *)
(*  Government and no official endorsement should be inferred.             *)
(*                                                                         *)
(***************************************************************************)

open !Core_kernel.Std
open OUnit2

module Lattice = Cbat_lattice_intf

module IntLattice : Lattice.S_val with type t = int = struct
  type t = int [@@deriving sexp, bin_io, compare]

  let pp = Int.pp

  let meet = min
  let join = max

  let bottom = Int.min_value
  let top = Int.max_value

  let widen_join a b = if a = b then a else top

  let equal = (=)
  let precedes = (<)

end

module Map = Cbat_map_lattice.Make_val(IntLattice)(IntLattice)

let test_add_bot _ =
  let add_1_j = Map.add Map.bottom ~key:0 ~data:1 in
  assert_equal ~cmp:Map.equal add_1_j Map.bottom

let test_join_add_bot _ =
  let add_1_j = Map.join_add Map.bottom ~key:3 ~data:(-1) in
  assert_equal ~cmp:Map.equal add_1_j Map.bottom

let test_meet_add_bot _ =
  let add_1_j = Map.meet_add Map.bottom ~key:23 ~data:(-21) in
  assert_equal ~cmp:Map.equal add_1_j Map.bottom

let test_find_bot _ =
  assert_equal ~cmp:IntLattice.equal
    (Map.find () Map.bottom 10)
    IntLattice.bottom

let test_meet_top_bot _ =
  assert_equal ~cmp:Map.equal
    (Map.meet Map.top Map.bottom)
    Map.bottom

let test_join_top_bot _ =
  assert_equal ~cmp:Map.equal
    (Map.join Map.top Map.bottom)
    Map.top

let test_meet_bot_top _ =
  assert_equal ~cmp:Map.equal
    (Map.meet Map.bottom Map.top)
    Map.bottom

let test_join_bot_top _ =
  assert_equal ~cmp:Map.equal
    (Map.join Map.bottom Map.top)
    Map.top

let test_meet_top_top _ =
  assert_equal ~cmp:Map.equal
    (Map.meet Map.top Map.top)
    Map.top

let test_join_top_top _ =
  assert_equal ~cmp:Map.equal
    (Map.join Map.top Map.top)
    Map.top

let test_meet_bot_bot _ =
  assert_equal ~cmp:Map.equal
    (Map.meet Map.bottom Map.bottom)
    Map.bottom

let test_join_bot_bot _ =
  assert_equal ~cmp:Map.equal
    (Map.join Map.bottom Map.bottom)
    Map.bottom

let test_add_find_k k _ =
  let data = 12343543 in
  let m1 = Map.add Map.top ~key:k ~data in
  let data' = Map.find () m1 k in
  assert_equal ~cmp:IntLattice.equal data data'

let test_add_find : test list =
  List.range (-100) 100
  |> List.map ~f:test_add_find_k
  |> List.map ~f:(test_case)


let all_tests =
 "map lattice tests">:::[
   "add element to bottom">::test_add_bot;
   "join-add element to bottom">::test_join_add_bot;
   "meet-add element to bottom">::test_meet_add_bot;
   "find element in bottom">::test_find_bot;
   "meet top and bottom">::test_meet_top_bot;
   "join top and bottom">::test_join_top_bot;
   "meet bottom and top">::test_meet_bot_top;
   "join bottom and top">::test_join_bot_top;
   "meet top and top">::test_meet_top_top;
   "join top and top">::test_join_top_top;
   "meet bottom and bottom">::test_meet_bot_bot;
   "join bottom and bottom">::test_join_bot_bot;
   "add followed by find">:::test_add_find;
]

