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
open Bap_core_theory

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

let init_mem ?(ogre = None) ?(init_mem = true) filename =
  if init_mem then
    let backend = Option.value ogre ~default:"llvm" in
    let res = Image.create ~backend filename in
    let img, _errs = Or_error.ok_exn res in
    Image.memory img
  else
    Memmap.empty

(* To reliably grab all known code addresses, we will need to fold over the
   disassembly state using `Disasm.Driver.explore`. Since this is a Knowledge
   computation, we need to create a dummy KB class to hold the result. *)
module Code_addrs = struct

  module Tree = Interval_tree.Make_binable(struct
      type t = addr * addr [@@deriving sexp, bin_io]
      type point = addr [@@deriving sexp, bin_io]

      let compare_point : point -> point -> int = Addr.compare

      let compare ((x1, y1) : t) ((x2, y2) : t) : int =
        match compare_point x1 x2 with
        | 0 -> compare_point y1 y2
        | n -> n

      let lower : t -> point = fst
      let upper : t -> point = snd
    end)

  type t = unit Tree.t [@@deriving bin_io]

  type cls

  let package = "wp"
  let name = "code-addrs-obj"

  let cls : (cls, unit) KB.cls = KB.Class.declare ~package name ()

  let domain : t option KB.domain = 
    KB.Domain.optional ~equal:(fun _ _ -> false) "code-addrs-domain"

  let slot : (cls, t option) KB.slot =
    KB.Class.property cls ~package "code-addrs" domain

  let empty : t = Tree.empty

  let collect (proj : project) : t =
    let open KB.Syntax in
    let t = Toplevel.eval slot @@
      let* obj = KB.Object.create cls in
      let tgt = Project.target proj in
      let width = Theory.Target.code_addr_size tgt in
      let addr_of_bitvec bv =
        Addr.of_int64 ~width @@ Bitvec.to_int64 bv in
      let state = Project.state proj in
      let entries =
        Set.to_sequence @@
        Disasm.Subroutines.entries @@
        Project.State.subroutines state in
      let disasm = Project.State.disassembly state in
      let block _ insns = KB.return @@ Disasm.Driver.list_insns insns in
      let node n acc = match List.hd n, List.last n with
        | Some start, Some end_ ->
          let* lower = start-->?Theory.Label.addr in
          let lower = addr_of_bitvec lower in
          let+ upper =
            let* addr = end_-->?Theory.Label.addr in
            let addr = addr_of_bitvec addr in
            let+ sem = end_-->Theory.Semantics.slot in
            (* Important to not get the end address, but instead the max
               address of the instruction, since our upper bound is
               inclusive. *)
            let len = match sem.$[Theory.Semantics.code] with
              | Some code -> String.length code - 1
              | None -> 0 in
            Addr.(addr + of_int len ~width) in
          Tree.add acc (lower, upper) ()
        | _ -> KB.return acc in
      let edge _ _ acc = KB.return acc in
      let* addrs = Disasm.Driver.explore disasm
          ~block ~node ~edge ~entries ~init:Tree.empty in
      let+ () = KB.provide slot obj @@ Some addrs in
      obj in
    Option.value_exn t

  let contains : t -> addr -> bool = Tree.contains

end
