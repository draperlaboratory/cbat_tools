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

let default_loader = "llvm"

let find_passes () : Project.pass list =
  (* Runs the passes set to autorun by default. (abi and api). *)
  let autorun = List.filter ~f:Project.Pass.autorun (Project.passes ()) in
  let with_no_return =
    match Project.find_pass "with-no-return" with
    | None -> warning "with-no-return pass is missing"; []
    | Some pass -> [pass]
  in
  autorun @ with_no_return

let run_passes (passes : Project.pass list) (proj : Project.t) : Project.t =
  List.fold passes ~init:proj ~f:(fun proj pass ->
      Project.Pass.run_exn pass proj)

(* Creates a BAP project from an input file. *)
let create_proj (state : Project.state option) (loader : string)
    (filename : string) : Project.t =
  let input = Project.Input.file ~loader ~filename in
  match Project.create ~package:filename ?state input with
  | Ok proj -> run_passes (find_passes ()) proj
  | Error e ->
    let msg = Error.to_string_hum e in
    failwith (Printf.sprintf "Error loading project: %s\n%!" msg)

(* Clears the attributes from the terms to remove unnecessary bloat and
   slowdown. We retain some important attributes:
   - the addresses for printing paths
   - the assembly instruction for handling instructions with unknown
      semantics *)
let clear_mapper : Term.mapper = object
  inherit Term.mapper as super
  method! map_term cls t =
    let add_attr tag dict =
      match Term.get_attr t tag with
      | None -> dict
      | Some attr -> Dict.set dict tag attr
    in
    let new_dict = Dict.empty |> add_attr address |> add_attr Disasm.insn in
    let t' = Term.with_attrs t new_dict in
    super#map_term cls t'
end

(* Reads in the program_t and its architecture from a file. *)
let read_program (ctxt : ctxt) ~(loader : string)
    ~(filepath : string) ~(collect_code_addrs : bool) : Cache.Program.t =
  let mk_digest = Cache.Digests.get_generator ctxt
      ~filepath ~loader ~collect_code_addrs in
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
    let code_addrs =
      if collect_code_addrs then
        project |> Bap_wp.Utils.Code_addrs.collect
      else Bap_wp.Utils.Code_addrs.empty in
    let prog = project |> Project.program |> clear_mapper#run in
    let tgt = Project.target project in
    let () = Cache.Program.save program_digest prog tgt code_addrs in
    prog, tgt, code_addrs
