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

(** [run params files ctxt] is the main entrypoint for WP. Based on the length
    of [files], it will run either a single or comparative analysis. If 0 or
    more than 2 files are given, an error is returned. [params] sets the
    properties WP will check and update default options. *)
val run : Parameters.t -> string list -> ctxt -> (unit, error) result
