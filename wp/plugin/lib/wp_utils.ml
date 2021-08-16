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
open Bap.Std
open Regular.Std
open Bap_knowledge

include Self()

module Cache = Wp_cache

let loader = "llvm"

(* Runs the passes set to autorun by default. (abi and api). *)
let autorun_passes (proj : Project.t) : Project.t =
  Project.passes ()
  |> List.filter ~f:Project.Pass.autorun
  |> List.fold ~init:proj ~f:(fun proj pass -> Project.Pass.run_exn pass proj)

(* Creates a BAP project from an input file. *)
let create_proj (state : Project.state option) (loader : string)
    (filename : string) : Project.t =
  let input = Project.Input.file ~loader ~filename in
  match Project.create ~package:filename ?state input with
  | Ok proj -> autorun_passes proj
  | Error e ->
    let msg = Error.to_string_hum e in
    failwith (Printf.sprintf "Error loading project: %s\n%!" msg)

let knowledge_reader = Data.Read.create
    ~of_bigstring:Knowledge.of_bigstring ()

let knowledge_writer = Data.Write.create
    ~to_bigstring:Knowledge.to_bigstring ()

let knowledge_cache () =
  Data.Cache.Service.request
    knowledge_reader
    knowledge_writer

let import_knowledge_from_cache digest =
  let digest = digest ~namespace:"knowledge" in
  info "looking for knowledge with digest %a"
    Data.Cache.Digest.pp digest;
  let cache = knowledge_cache () in
  match Data.Cache.load cache digest with
  | None -> false
  | Some state ->
    info "importing knowledge from cache";
    Toplevel.set state;
    true

let store_knowledge_in_cache digest =
  let digest = digest ~namespace:"knowledge" in
  info "caching knowledge with digest %a"
    Data.Cache.Digest.pp digest;
  let cache = knowledge_cache () in
  Toplevel.current () |>
  Data.Cache.save cache digest

let save_knowledge ~had_knowledge digest =
  if not had_knowledge
  then store_knowledge_in_cache digest
  else ()


(* Reads in the project from a file, creating a cache if none exists. *)
let read_project (ctxt : ctxt) ~(loader : string) ~(filepath : string)
  : Project.t =
  let digest = Cache.Digests.generator ctxt ~filepath ~loader in
  let had_knowledge = import_knowledge_from_cache digest in
  let proj = create_proj None loader filepath in
  save_knowledge ~had_knowledge digest;
  proj
