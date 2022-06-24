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

(**

   This module is the runner for WP. It will run either a single or comparative
   analysis based on the number of files inputted by the user.

*)

open Bap_main
open Bap.Std
open Bap_core_theory

module Params = Run_parameters

(** The program data.

    - [program] is the program to be checked.
    - [code_addrs] is a hash set of addresses that are known to point to
      executable code (excludes inlined data in the code sections).
    - [target] is the target machine.
    - [filename] is the filename of the program.
*)
type input =
  {
    program : program term;
    code_addrs : Addr.Set.t;
    target : Theory.target;
    filename : string;
  }

(** [run params files ctxt] is the main entrypoint for WP. Based on the length
    of [files], it will run either a single or comparative analysis. If 0 or
    more than 2 files are given, an error is returned. [params] sets the
    properties WP will check and update default options. *)
val run :
  Params.t
  -> input list
  -> (Z3.Solver.status, error) result
