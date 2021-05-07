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
open Bap.Std

(* FIXME: can we remove this include? *)
include Self()

module Option_let = struct

  let (let*) (x : 'a option) (f : 'a -> 'b option) : 'b option =
    Option.bind x ~f

  let (let+) (x : 'a option) (f : 'a -> 'b) : 'b option =
    Option.map x ~f

end

let varset_to_string (vs : Var.Set.t) : string =
  vs
  |> Var.Set.to_sequence
  |> Seq.to_list
  |> List.to_string ~f:Var.to_string

let find_func_err (subs : Sub.t Seq.t) (func : string) : Sub.t =
  match Seq.find ~f:(fun s -> String.equal (Sub.name s) func) subs with
  | None ->
    let msg = Printf.sprintf "Missing function: %s is not in binary.%!" func in
    raise @@ Not_found_s (Sexp.Atom msg)
  | Some f -> f

let get_mod_func_name  (re : (string * string) list) (name_orig : string)
  : string option =
  if List.is_empty re then
    Some name_orig
  else
    List.find_map (List.rev re)
      ~f:(fun (orig, modif) ->
          let regexp = Str.regexp orig in
          if Str.string_match regexp name_orig 0 then
            Some (Str.replace_first regexp modif name_orig)
          else
            None)

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
