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

open OUnit2;;
open Cbat_value_set

module ClpSet = Cbat_clp_set_composite;;
module TestComposite = Clp_test.Make(ClpSet)(ClpSet);;
module TestClp = Clp_test.Make(Cbat_clp)(struct let of_clp = fun x -> x end);;

run_test_tt_main begin "All tests">:::[
    Word_ops_test.all_tests;
    TestClp.all_tests;
    TestComposite.all_tests;
    Map_lattice_test.all_tests;
    Ai_memmap_test.all_tests;
] end;;

