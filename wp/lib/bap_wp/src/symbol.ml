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

module Bool = Z3.Boolean
module BV = Z3.BitVector
module Expr = Z3.Expr
module Constr = Constraint
module Pre = Precondition

type t = string * Word.t

let build_command (filename : string) : string =
  Format.sprintf "objdump -t %s | sed '0,/SYMBOL TABLE:/d' | grep -E 'data|bss' | awk '{print $1, $NF}'" filename

let run_command (cmd : string) : string list =
  let inp = Unix.open_process_in cmd in
  let r = In_channel.input_lines inp in
  In_channel.close inp; r

let parse_result (output : string list) : t list =
  output
  |> List.sort ~compare:String.compare
  |> List.rev
  |> List.fold ~init:[]
    ~f:(fun symbols line ->
        match String.split ~on:' ' line with
        | [addr; name] ->
          let width = (String.length addr) * 4 in
          let bap_addr = Word.of_string (Format.sprintf "0x%s:%d" addr width) in
          (name, bap_addr) :: symbols
        | _ -> symbols
      )

let get_symbols (filename : string) : t list =
  filename
  |> build_command
  |> run_command
  |> parse_result

(* Converts the type of addresses in [t] from Word.t to Constr.z3_expr. *)
let addrs_to_z3 (ctx : Z3.context) (syms : t list) : (string * Constr.z3_expr) list =
  List.map syms ~f:(fun (name, addr) -> (name, Pre.word_to_z3 ctx addr))

(* [find pre syms] finds the symbol in [syms] whose name contains the prefix [pre]. *)
let find (prefix : string) (syms : (string * Constr.z3_expr) list)
  : (string * Constr.z3_expr) option =
  List.find syms ~f:(fun (name, _) -> String.is_prefix name ~prefix)

let offset_constraint ~orig:(syms_orig : t list) ~modif:(syms_mod : t list)
    (ctx : Z3.context) : Constr.z3_expr -> Constr.z3_expr =
  let syms_orig = addrs_to_z3 ctx syms_orig in
  let syms_mod = addrs_to_z3 ctx syms_mod in
  fun addr ->
    let rec calc_offsets syms_orig offsets =
      match syms_orig with
      | (name, addr_start_orig) :: ((_, addr_end_orig) :: _ as ss) ->
        begin
          match find name syms_mod with
          | None -> calc_offsets ss offsets
          | Some (_, addr_mod) ->
            begin
              let in_range = Bool.mk_and ctx [BV.mk_ule ctx addr_start_orig addr;
                                              BV.mk_ult ctx addr addr_end_orig] in
              let diff = BV.mk_sub ctx addr_mod addr_start_orig in
              calc_offsets ss (Bool.mk_ite ctx in_range (BV.mk_add ctx addr diff) offsets)
            end
        end
      | [] | _ :: [] -> offsets
    in
    calc_offsets syms_orig addr
