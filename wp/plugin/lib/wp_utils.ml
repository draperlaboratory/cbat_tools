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
open Bap_core_theory

include Self()

module Env = Environment
module Pre = Precondition
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

let spec_of_name (name : string) : Sub.t -> Theory.target -> Env.fun_spec option =
  match name with
  | "verifier-error" -> Pre.spec_verifier_error
  | "verifier-assume" -> Pre.spec_verifier_assume
  | "verifier-nondet" -> Pre.spec_verifier_nondet
  | "afl-maybe-log" -> Pre.spec_afl_maybe_log
  | "arg-terms" -> Pre.spec_arg_terms
  | "chaos-caller-saved" -> Pre.spec_chaos_caller_saved
  | "chaos-rax" -> Pre.spec_chaos_rax
  | "rax-out" -> Pre.spec_rax_out
  | "empty" -> Pre.spec_empty
  | name ->
    (* TODO: We should return an error here instead of failing directly, but
       that would require some code cleanup on the analysis side. *)
    let err = Printf.sprintf "'%s' is not a supported spec. See `bap wp \
                              --help' for available function specs.%!" name in
    failwith err

(* Creates a map of modified subroutine names to original subroutine names
   based off the regex from the user. *)
let mk_func_name_map
    ~orig:(subs_orig : Sub.t Seq.t)
    ~modif:(subs_mod : Sub.t Seq.t)
    (re : (string * string) list)
  : string String.Map.t =
  let re = List.rev re in
  Seq.fold subs_orig ~init:String.Map.empty ~f:(fun map sub_orig ->
      let name_orig = Sub.name sub_orig in
      List.fold re ~init:map ~f:(fun m (orig, modif) ->
          let regexp = Str.regexp orig in
          let name_mod = Str.replace_first regexp modif name_orig in
          let in_orig = Str.string_match regexp name_orig 0 in
          let in_mod = Seq.exists subs_mod ~f:(fun s ->
              String.equal (Sub.name s) name_mod) in
          if in_orig && in_mod then
            String.Map.set m ~key:name_mod ~data:name_orig
          else
            m))

(* Determines the name of the modified subroutine based off of the original
   subroutine's name and the regex from the user. We raise an exception if we
   can't find a subroutine that matches the regex. *)
let get_mod_func_name (name_orig : string) (re : (string * string) list)
  : string option =
  if List.is_empty re then
    Some name_orig
  else
    List.find_map (List.rev re) ~f:(fun (orig, modif) ->
        let regexp = Str.regexp orig in
        if Str.string_match regexp name_orig 0 then
          Some (Str.replace_first regexp modif name_orig)
        else
          None)
