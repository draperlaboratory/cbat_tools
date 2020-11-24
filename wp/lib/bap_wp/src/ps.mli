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

(** A utility for running shell commands. *)

module Cmd : sig

  (** Runs a command in a shell, returns the exit code, stdout, and stderr.

      Arguments:
      - A string (the command to execute in the shell)

      Returns: a triple composed of:
      - The exit code (an int)
      - The command's stdout (a string)
      - The command's stderr (a string) *)
  val run : string -> int * string * string

end
