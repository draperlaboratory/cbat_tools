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

module Bool = Z3.Boolean
module BV = Z3.BitVector
module Expr = Z3.Expr
module Constr = Constraint

type symbol = string * Constr.z3_expr

let build_command (filename : string) : string =
  Format.sprintf "objdump -t %s | sed '0,/SYMBOL TABLE:/d' | grep -E 'data|bss' | awk '{print $1, $NF}'" filename

let run_command (cmd : string) : string list =
  let inp = Unix.open_process_in cmd in
  let r = In_channel.input_lines inp in
  In_channel.close inp; r

let parse_result (ctx : Z3.context) (output : string list) : symbol list =
  output
  |> List.sort ~compare:String.compare
  |> List.rev
  |> List.fold ~init:[]
    ~f:(fun symbols line ->
        match String.split ~on:' ' line with
        | [addr; name] ->
          let width = (String.length addr) * 4 in
          (* Convert the addr string from hex to dec *)
          let addr = "0x" ^ addr |> int_of_string |> string_of_int in
          let z3_addr = BV.mk_numeral ctx addr width in
          (name, z3_addr) :: symbols
        | _ -> symbols
      )

let get_symbols (ctx : Z3.context) (filename : string) : symbol list =
  filename
  |> build_command
  |> run_command
  |> parse_result ctx

let get_offsets (ctx : Z3.context) (syms_orig : symbol list) (syms_mod : symbol list)
  : Constr.z3_expr -> Constr.z3_expr =
  fun addr ->
  let rec calc_offsets syms_orig offsets =
    match syms_orig with
    | (name_orig, addr_begin_orig) :: ((_, addr_end_orig) :: _ as ss) ->
      begin
        let sym_match = List.find syms_mod
            ~f:(fun (name_mod, _) ->
                String.is_prefix name_mod ~prefix:name_orig)
        in
        match sym_match with
        | None -> calc_offsets ss offsets
        | Some (_, addr_mod) ->
          begin
            let in_range = Bool.mk_and ctx [BV.mk_ule ctx addr_begin_orig addr;
                                            BV.mk_ult ctx addr addr_end_orig] in
            let diff = BV.mk_sub ctx addr_mod addr_begin_orig in
            calc_offsets ss (Bool.mk_ite ctx in_range (BV.mk_add ctx addr diff) offsets)
          end
      end
    | [] | _ :: [] -> offsets
  in
  calc_offsets syms_orig addr
