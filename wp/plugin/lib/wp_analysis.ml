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
open Bap_main
open Bap_wp

module Params = Run_parameters
module Utils = Wp_utils

(* Entrypoint for the WP analysis. *)
let run (p : Params.t) (files : string list) (bap_ctx : ctxt)
  : (Z3.Solver.status, error) result =

  let files_and_ogres : (string * string option) list =
    let open Params in
    let loader_1 = Option.first_some p.ogre p.ogre_orig in
    let loader_2 = Option.first_some p.ogre p.ogre_mod in
    List.mapi files ~f:(fun i f ->
        match i with
        | 0 -> (f,loader_1)
        | 1 -> (f,loader_2)
        | _ -> (f,None))
  in

  (* Unbundle the input file into its loaded program *)
  let mk_input (file,loader) =
    let prog, tgt, code_addrs =
      Utils.read_program
        bap_ctx
        ~loader:(Option.value loader ~default:Utils.default_loader)
        ~filepath:file
        ~collect_code_addrs:p.Params.init_mem
    in
    Runner.{
      program = prog;
      code_addrs;
      target = tgt;
      filename = file;
    }
  in

  let input_list = List.map files_and_ogres ~f:mk_input in
  Runner.run p input_list
