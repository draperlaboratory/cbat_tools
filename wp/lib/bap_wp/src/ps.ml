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

(** Implements {!Ps}. *)

module Proc = struct

  let int_of_status (s : Unix.process_status) : int =
    match s with
    | Unix.WEXITED n -> n
    | Unix.WSIGNALED n -> n
    | Unix.WSTOPPED n -> n

  let shell (cmd : string) (out : Unix.file_descr) (err : Unix.file_descr) : int =
    match Unix.fork () with
    | 0 ->
      Unix.dup2 out Unix.stdout;
      Unix.close out;
      Unix.dup2 err Unix.stderr;
      Unix.close err;
      Unix.execvp "/bin/sh" [| "/bin/sh"; "-c"; cmd |]
    | pid -> pid

  let popen (cmd : string) : int * in_channel * in_channel =
    let (stdout_read, stdout_write) = Unix.pipe ~cloexec:true () in
    let (stderr_read, stderr_write) =
      try Unix.pipe ~cloexec:true ()
      with e ->
        Unix.close stdout_read;
        Unix.close stdout_write;
        raise e in
    Unix.set_nonblock stdout_read;
    Unix.set_nonblock stderr_read;
    let out_ch = Unix.in_channel_of_descr stdout_read in
    let err_ch = Unix.in_channel_of_descr stderr_read in
    begin
      try
        let pid = shell cmd stdout_write stderr_write in
        Unix.close stdout_write;
        Unix.close stderr_write;
        (pid, out_ch, err_ch)
      with e ->
        Unix.close stdout_read; Unix.close stdout_write;
        Unix.close stderr_read; Unix.close stderr_write;
        raise e;
    end

  let poll (pid : int) : int option =
    let pid', s = Unix.waitpid [Unix.WNOHANG] pid in
    match pid' with
    | 0 -> None
    | _ -> Some (int_of_status s)

end


module Buff = struct

  type t = { channel : in_channel; buffer : Buffer.t }

  let create (channel : in_channel) : t =
    { channel; buffer = Buffer.create 80 }

  let fill (t : t) : unit =
    try
      while true do
        Buffer.add_channel t.buffer t.channel 1
      done
    with
    | Sys_blocked_io -> ()
    | End_of_file -> ()

  let contents (t : t) : string =
    Buffer.contents t.buffer

end


module Cmd = struct

  let collect_output (out_buf : Buff.t) (err_buf : Buff.t) : unit =
    Buff.fill out_buf; Buff.fill err_buf

  let rec while_waiting (pid : int) (out_buf : Buff.t) (err_buf : Buff.t) : int =
    match Proc.poll pid with
    | None ->
      collect_output out_buf err_buf;
      Unix.sleepf 0.25;
      while_waiting pid out_buf err_buf
    | Some n ->
      collect_output out_buf err_buf;
      n

  let run (cmd : string) : int * string * string =
    let pid, stdout_ch, stderr_ch = Proc.popen cmd in
    let out_buf = Buff.create stdout_ch in
    let err_buf = Buff.create stderr_ch in
    let exit_code = while_waiting pid out_buf err_buf in
    close_in stdout_ch;
    close_in stderr_ch;
    let out = Buff.contents out_buf in
    let err = Buff.contents err_buf in
    (exit_code, out, err)

end
