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
open Bap_core_theory
open Bap.Std
open Regular.Std

module Digests = struct

  module Conf = Extension.Configuration

  (* Returns a function that makes digests. *)
  let get_generator (ctx : ctxt) ~(filepath : string) ~(loader : string)
    : namespace:string -> digest =
    let inputs = [Conf.digest ctx; Caml.Digest.file filepath; loader] in
    let subject = String.concat inputs in
    fun ~namespace ->
      let d = Data.Cache.Digest.create ~namespace in
      Data.Cache.Digest.add d "%s" subject

  (* Creates a digest for the knowledge cache. *)
  let knowledge (mk_digest : namespace:string -> digest) : digest =
    mk_digest ~namespace:"knowledge"

  (* Creates a digest for the project state cache. *)
  let project (mk_digest : namespace:string -> digest) : digest =
    mk_digest ~namespace:"project"

  (* Creates a digest for the program state cache. *)
  let program (mk_digest : namespace:string -> digest) : digest =
    mk_digest ~namespace:"program"

end

module Knowledge = struct

  (* Creates the knowledge cache. *)
  let knowledge_cache () : KB.state Data.Cache.t =
    let reader = Data.Read.create ~of_bigstring:KB.of_bigstring () in
    let writer = Data.Write.create ~to_bigstring:KB.to_bigstring () in
    Data.Cache.Service.request reader writer

  (* Loads knowledge (if any) from the knowledge cache. *)
  let load (digest : digest) : unit =
    let cache = knowledge_cache () in
    match Data.Cache.load cache digest with
    | None -> ()
    | Some state -> Toplevel.set state

  (* Saves knowledge in the knowledge cache. *)
  let save (digest : digest) : unit =
    let cache = knowledge_cache () in
    Toplevel.current ()
    |> Data.Cache.save cache digest

end

module Project = struct

  (* Creates a project state cache. *)
  let project_cache () : Project.state Data.Cache.t =
    let module State = struct
      type t = Project.state [@@deriving bin_io]
    end in
    let of_bigstring = Binable.of_bigstring (module State) in
    let to_bigstring = Binable.to_bigstring (module State) in
    let reader = Data.Read.create ~of_bigstring () in
    let writer = Data.Write.create ~to_bigstring () in
    Data.Cache.Service.request reader writer

  (* Loads project state (if any) from the cache. *)
  let load (digest : digest) : Project.state option =
    let cache = project_cache () in
    Data.Cache.load cache digest

  (* Saves project state in the cache. *)
  let save (digest : digest) (state : Project.state) : unit =
    let cache = project_cache () in
    Data.Cache.save cache digest state

end

module Program = struct

  type t =
    Program.t *
    Theory.Target.t *
    Bap_wp.Utils.Code_addrs.t
  [@@deriving bin_io]

  (* Creates a program cache. *)
  let program_cache () : t Data.Cache.t =
    let module Prog = struct
      type nonrec t = t [@@deriving bin_io]
    end in
    let of_bigstring = Binable.of_bigstring (module Prog) in
    let to_bigstring = Binable.to_bigstring (module Prog) in
    let reader = Data.Read.create ~of_bigstring () in
    let writer = Data.Write.create ~to_bigstring () in
    Data.Cache.Service.request reader writer

  (* Loads a program and its architecture (if any) from the cache. *)
  let load (digest : digest) : t option =
    let cache = program_cache () in
    Data.Cache.load cache digest

  (* Saves a program and its architecture in the cache. *)
  let save (digest : digest) (program : Program.t) (tgt : Theory.Target.t)
      (code_addrs : Bap_wp.Utils.Code_addrs.t) : unit =
    let cache = program_cache () in
    Data.Cache.save cache digest (program, tgt, code_addrs)

end
