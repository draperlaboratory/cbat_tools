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
open Bap_main
open Regular.Std

module Digests = struct

  module Conf = Extension.Configuration

  (* Returns a function that makes digests. *)
  let generator (ctx : ctxt) ~(filepath : string) ~(loader : string)
    : namespace:string -> digest =
    let inputs = [Conf.digest ctx; Caml.Digest.file filepath; loader] in
    let subject = String.concat inputs in
    fun ~namespace ->
      let d = Data.Cache.Digest.create ~namespace in
      Data.Cache.Digest.add d "%s" subject

end
