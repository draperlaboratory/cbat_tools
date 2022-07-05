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

open !Core
open Bap.Std

module Bool = Z3.Boolean
module BV = Z3.BitVector
module Expr = Z3.Expr
module Env = Environment
module Constr = Constraint
module Pre = Precondition

exception ExecutionError of string
exception NonzeroExit of string

include Self()

type t = string * Word.t

let build_command (filename : string) : string =
  Format.sprintf "objdump -t %s | sed '0,/SYMBOL TABLE:/d' | grep -E 'data|bss' | awk '{print $1, $NF}'" filename

let exec_err (cmd : string) (e : exn) : string =
  Format.sprintf "Couldn't run command '%s'.\nError: %s%!" cmd (Exn.to_string e)

let cmd_err (cmd : string) (code : int) (out : string) (err : string) : string =
  Format.sprintf "Command exited with non-zero exit code.\nCMD: '%s'\n \
                 EXIT CODE: '%d'\nSTDOUT: %s\nSTDERR: %s%!" cmd code out err

let run_command (cmd : string) : string =
  let code, out, err = try
      Ps.Cmd.run cmd
    with e ->
      let msg = exec_err cmd e in
      raise (ExecutionError msg)
  in
  match code with
  | 0 -> out
  | n ->
    let msg = cmd_err cmd n out err in
    raise (NonzeroExit msg)

let parse_result (output : string) : t list =
  output
  |> String.split ~on:'\n'
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

(* In retrowrite, a symbol's name could either be the same as the original or be
   appended with an underscore and the original address. *)
let retrowrite_pattern (name : string) : Re__.Core.re =
  Format.sprintf "^%s(_[a-fA-F0-9]+)?$" name
  |> Re.Posix.re
  |> Re.Posix.compile

let offset_constraint ~orig:(syms_orig : t list) ~modif:(syms_mod : t list)
    (ctx : Z3.context) : Constr.z3_expr -> Constr.z3_expr =
  let syms_orig = addrs_to_z3 ctx syms_orig in
  let syms_mod = addrs_to_z3 ctx syms_mod in
  (* Finds the symbol in the modified binary that matches the retrowrite pattern
     on its name. *)
  let find name_orig syms =
    List.find syms ~f:(fun (name_mod, _) ->
        Re.execp (retrowrite_pattern name_orig) name_mod)
  in
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

let update_address ~orig:(syms_orig : t list) ~modif:(syms_mod : t list)
  : Word.t -> Word.t =
  (* Find the symbol in the original binary that matches that of the modified
     binary. *)
  let find name_mod syms =
    List.find syms ~f:(fun (name_orig, _) ->
        Re.execp (retrowrite_pattern name_orig) name_mod)
  in
  fun addr ->
    let rec rewrite syms_mod =
      match syms_mod with
      | (name_mod, addr_start_mod) :: ((_, addr_end_mod) :: _ as ss) -> begin
          match find name_mod syms_orig with
          | None -> rewrite ss
          | Some (name_orig, addr_orig) ->
            if Word.(addr_start_mod <= addr && addr < addr_end_mod) then
              let diff = Word.(addr_start_mod - addr_orig) in
              let ptr = Word.(addr - diff) in
              info "Rewriting pointer from %s:%s to %s:%s%!"
                name_mod (Word.to_string addr) name_orig (Word.to_string ptr);
              ptr
            else
              rewrite ss
        end
      | [] | _ :: [] -> addr
    in
    rewrite syms_mod

let rewrite_addresses ~(orig : t list) ~(modif : t list) (sub : Sub.t) : Sub.t =
  let update_exp = object
    inherit Exp.mapper as super
    method! map_int word =
      let word' = update_address ~orig ~modif word in
      super#map_int word'
  end in
  Term.map blk_t sub ~f:(Blk.map_exp ~f:(Exp.map update_exp))
