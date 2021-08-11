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

(* Clears the attributes from the terms to remove unnecessary bloat and
   slowdown. We retain the addresses for printing paths. *)
let clear_mapper : Term.mapper = object
  inherit Term.mapper as super
  method! map_term cls t =
    let new_dict =
      Option.value_map (Term.get_attr t address)
        ~default:Dict.empty
        ~f:(Dict.set Dict.empty address)
    in
    let t' = Term.with_attrs t new_dict in
    super#map_term cls t'
end

(* FIXME: read context to determine whether we need the "fat" project or not. *)
let is_skinny (_ctxt : ctxt) = false

(* Make a "skinny" project with nothing in it *)
let mk_skinny (proj : project) : project =
  let tgt = Project.target proj in
  let empty = Project.empty tgt in
  let skinny_prog = proj |> Project.program |> clear_mapper#run in
  let with_prog = Project.with_program empty skinny_prog in
  with_prog

(* Reads in the project from a file, creating a cache if none exists. *)
let read_project (ctxt : ctxt) ~(loader : string) ~(filepath : string)
  : Project.t =
  let mk_digest = Cache.Digests.generator ctxt ~filepath ~loader in
  let project_digest = Cache.Digests.project mk_digest in
  match Project.Cache.load project_digest with
  | Some project ->
    info "Program %s (%a) found in cache.%!"
      filepath Data.Cache.Digest.pp project_digest;
    project
  | None ->
    (* The program_t is not in the cache. Disassemble the binary. *)
    info "Saving program %s (%a) to cache.%!"
      filepath Data.Cache.Digest.pp project_digest;
    let project = create_proj None loader filepath in
    (* If needed, replace the project with the "skinny" version *)
    let project =
      if is_skinny ctxt then
        mk_skinny project
      else
        project
    in
    let () = Project.Cache.save project_digest project in
    project
