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
open Bap_core_theory

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
   slowdown. We rain the addresses for printing paths. *)
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

(* Reads in the program_t and its architecture from a file. *)
let read_program (ctxt : ctxt) ~(loader : string) ~(filepath : string)
  : Program.t * Theory.target =
  let mk_digest = Cache.Digests.get_generator ctxt ~filepath ~loader in
  let program_digest = Cache.Digests.program mk_digest in
  match Cache.Program.load program_digest with
  | Some prog ->
    info "Program %s (%a) found in cache.%!"
      filepath Data.Cache.Digest.pp program_digest;
    prog
  | None ->
    (* The program_t is not in the cache. Disassemble the binary. *)
    info "Saving program %s (%a) to cache.%!"
      filepath Data.Cache.Digest.pp program_digest;
    let project = create_proj None loader filepath in
    let prog = project |> Project.program |> clear_mapper#run in
    let tgt = Project.target project in
    let () = Cache.Program.save program_digest prog tgt in
    prog, tgt
