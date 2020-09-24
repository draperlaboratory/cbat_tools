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
open Bap_wp

include Self()

module Env = Environment
module Pre = Precondition

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
    : Program.t * Arch.t =
  let mk_digest = Cache.Digests.get_generator ctxt ~filepath ~loader in
  let knowledge_digest = Cache.Digests.knowledge mk_digest in
  let () = Cache.Knowledge.load knowledge_digest in
  match Cache.Program.load filepath with
  | Some prog ->
    info "Program %s (%a) found in cache.%!"
      filepath Data.Cache.Digest.pp knowledge_digest;
    prog, Option.value_exn (Cache.Arch.load filepath)
  | None ->
    (* The program_t is not in the cache. Disassemble the binary. *)
    info "Saving program %s (%a) to cache.%!"
      filepath Data.Cache.Digest.pp knowledge_digest;
    let project = create_proj None loader filepath in
    let prog = project |> Project.program |> clear_mapper#run in
    let arch = Project.arch project in
    let () = Toplevel.reset () in
    let () = Cache.Program.save filepath prog in
    let () = Cache.Arch.save filepath arch in
    let () = Cache.Knowledge.save knowledge_digest in
    prog, arch

(* Finds a function in the binary. *)
let find_func_err (subs : Sub.t Seq.t) (func : string) : Sub.t =
  match Seq.find ~f:(fun s -> String.equal (Sub.name s) func) subs with
  | None ->
    let msg = Printf.sprintf "Missing function: %s is not in binary.%!" func in
    failwith msg
  | Some f -> f

(* Finds a sequence of subroutines to inline based on the regex from the
   user. *)
let match_inline (to_inline : string option) (subs : Sub.t Seq.t)
  : Sub.t Seq.t =
  match to_inline with
  | None -> Seq.empty
  | Some to_inline ->
    let inline_pat = Re.Posix.re to_inline |> Re.Posix.compile in
    let filter_subs =
      Seq.filter ~f:(fun s -> Re.execp inline_pat (Sub.name s)) subs
    in
    let () =
      if Seq.is_empty filter_subs then
        warning "No matches on inlining. Regex: %s\n%!%!" to_inline
      else
        info "Inlining functions: %s%!\n"
          (filter_subs |> Seq.to_list |> List.to_string ~f:Sub.name)
    in
    filter_subs

(* Converts a set of variables to a string for printing debug logs. *)
let varset_to_string (vs : Var.Set.t) : string =
  vs
  |> Var.Set.to_sequence
  |> Seq.to_list
  |> List.to_string ~f:Var.to_string

(* Updates the number of times to unroll a loop based on the user's input. *)
let update_default_num_unroll (num_unroll : int option) : unit =
  match num_unroll with
  | Some n -> Pre.num_unroll := n
  | None -> ()

(* Updates the stack's base/size based on the user's input. *)
let update_stack ~(base : int option) ~(size : int option) : Env.mem_range =
  let update_base stack_base range =
    match stack_base with
    | None -> range
    | Some base -> Env.update_stack_base range base in
  let update_size stack_size range =
    match stack_size with
    | None -> range
    | Some size -> Env.update_stack_size range size in
  Pre.default_stack_range
  |> update_base base
  |> update_size size

(* Checks the user's input for outputting a gdb script. *)
let output_to_gdb ~(filename : string option) ~(func : string)
    (solver : Z3.Solver.solver) (status : Z3.Solver.status) (env : Env.t)
  : unit =
  match filename with
  | None -> ()
  | Some name -> Output.output_gdb ~filename:name ~func solver status env

(* Checks the user's input for outputting a bildb script. *)
let output_to_bildb ~(filename : string option) (solver : Z3.Solver.solver)
    (status : Z3.Solver.status) (env : Env.t) : unit =
 match filename with
  | None -> ()
  | Some name -> Output.output_bildb solver status env name
