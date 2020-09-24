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
open KB.Let_syntax

module Digests = struct

  module Conf = Extension.Configuration

  (* Returns a function that makes digests. *)
  let get_generator ctx ~filepath ~loader =
    let inputs = [Conf.digest ctx; Caml.Digest.file filepath; loader] in
    let subject = String.concat inputs in
    fun ~namespace ->
      let d = Data.Cache.Digest.create ~namespace in
      Data.Cache.Digest.add d "%s" subject

  (* Creates a digest for the knowledge cache. *)
  let knowledge mk_digest = mk_digest ~namespace:"knowledge"

  (* Creates a digest for the project state cache. *)
  let project mk_digest = mk_digest ~namespace:"project"

end

module Knowledge = struct

  (* Creates the knowledge cache. *)
  let knowledge_cache () =
    let reader = Data.Read.create ~of_bigstring:KB.of_bigstring () in
    let writer = Data.Write.create ~to_bigstring:KB.to_bigstring () in
    Data.Cache.Service.request reader writer

  (* Loads knowledge (if any) from the knowledge cache. *)
  let load digest : unit =
    let cache = knowledge_cache () in
    match Data.Cache.load cache digest with
    | None -> ()
    | Some state -> Toplevel.set state

  (* Saves knowledge in the knowledge cache. *)
  let save digest : unit =
    let cache = knowledge_cache () in
    Toplevel.current ()
    |> Data.Cache.save cache digest

end

module Project = struct

  (* Creates a project state cache. *)
  let project_cache () =
    let module State = struct
      type t = Project.state [@@deriving bin_io]
    end in
    let of_bigstring = Binable.of_bigstring (module State) in
    let to_bigstring = Binable.to_bigstring (module State) in
    let reader = Data.Read.create ~of_bigstring () in
    let writer = Data.Write.create ~to_bigstring () in
    Data.Cache.Service.request reader writer

  (* Loads project state (if any) from the cache. *)
  let load digest : Project.state option =
    let cache = project_cache () in
    Data.Cache.load cache digest

  (* Saves project state in the cache. *)
  let save digest state : unit =
    let cache = project_cache () in
    Data.Cache.save cache digest state

end

module Program = struct

  let package = "program"

  (* Gives a unique name to a KB object from the filename of the program. *)
  let for_program filename =
    KB.Symbol.intern filename Theory.Unit.cls ~package ~public:true

  (* Creates an optional domain for programs. *)
  let program_t = KB.Domain.optional "program_t" ~equal:Program.equal

  (* Creates a persistent program slot for the KB that is preserved between
     program runs. *)
  let program =
    let module Program = struct
      type t = Program.t option [@@deriving bin_io]
    end in
    KB.Class.property Theory.Unit.cls "program" program_t
      ~package
      ~public:true
      ~desc:"The program term under analysis."
      ~persistent:(KB.Persistent.of_binable (module Program))

  (* Obtains the program from the KB. *)
  let load file : Program.t option =
    let obj = for_program file in
    let state = Toplevel.current () in
    match KB.run Theory.Unit.cls obj state with
    | Ok (value, _) -> KB.Value.get program value
    | Error c ->
      let msg = Format.asprintf "Unable to collect program_t: %a%!"
          KB.Conflict.pp c in
      failwith msg

  (* Adds the program_t to the KB. *)
  let save file prog : unit =
    let obj =
      for_program file >>= fun label ->
      KB.provide program label (Some prog) >>| fun () ->
      label in
    let state = Toplevel.current () in
    match KB.run Theory.Unit.cls obj state with
    | Ok (_, state) -> Toplevel.set state
    | Error c ->
      let msg = Format.asprintf "Unable to provide program_t: %a%!"
          KB.Conflict.pp c in
      failwith msg

end

module Arch = struct

  (* Obtains the program's architecture from the KB. *)
  let load file : Arch.t option =
    let obj = Theory.Unit.for_file file in
    let state = Toplevel.current () in
    match KB.run Theory.Unit.cls obj state with
    | Ok (value, _) ->
      value
      |> KB.Value.get Theory.Unit.Target.arch
      |> Option.bind ~f:Arch.of_string
    | Error c ->
      let msg = Format.asprintf "Unable to collect arch: %a%!"
          KB.Conflict.pp c in
      failwith msg

  (* Adds the program's architecture to the KB. *)
  let save file arch : unit =
    let obj =
      Theory.Unit.for_file file >>= fun label ->
      let arch = Arch.to_string arch in
      KB.provide Theory.Unit.Target.arch label (Some arch) >>| fun () ->
      label in
    let state = Toplevel.current () in
    match KB.run Theory.Unit.cls obj state with
    | Ok (_, state) -> Toplevel.set state
    | Error c ->
      let msg = Format.asprintf "Unable to provide architecture: %a%!"
          KB.Conflict.pp c in
      failwith msg

end

