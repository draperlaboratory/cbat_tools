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
include Self()


let main nm proj : unit =
  let prog = Project.program proj in
  let dest =
    match (nm, Project.get proj filename) with
    | ("", None) ->
      Format.printf "Please specify a destination filename with --save-project-filename.\n";
      exit 1;
    | ("", Some bnm) -> String.concat [bnm; ".bpj"]
    | (user_dest, _) -> user_dest
  in
  Program.Io.write ~fmt:"bin" dest prog

module Cmdline = struct
  open Config
  let filename = param string "filename" ~doc:"Name of output file"

  let () = when_ready (fun {get=(!!)} ->
      Project.register_pass' (main !!filename))

  let () = manpage [
      `S "DESCRIPTION";
      `P "Saves a binary's program data structure to disk."
    ]
end
