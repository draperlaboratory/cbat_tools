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

include Bap.Std

module W = Word
module Clp = Cbat_clp

let be_silent = Array.length Sys.argv > 1

let print = if be_silent then fun _ -> ()  else print_string

let test_ppf = if be_silent
  then Format.make_formatter (fun _ _ _ -> ()) (fun () -> ())
  else Format.std_formatter

let test_clps i =
  let wd = W.of_int ~width:i in
  let mx = W.ones (i + 1) in
  [Clp.create (wd (-56)) ~step:(wd 32) ~cardn:(wd 999);
   Clp.create (wd 45)  ~step:(wd 0) ~cardn:(wd 9);
   Clp.create (wd 245)  ~step:(wd 5644) ~cardn:(wd 5);
   Clp.create (wd 139)  ~step:(wd 64) ~cardn:(wd 65);
   Clp.create (wd 13)  ~step:(wd 4) ~cardn:mx;
   Clp.create (wd (-25))  ~step:(wd 1) ~cardn:mx;
   Clp.create (wd 654)  ~step:(wd 0) ~cardn:mx]

let test_clps_32 = test_clps 32
let test_clps_64 = test_clps 64
