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

include Self()

module Expr = Z3.Expr
module Arith = Z3.Arithmetic
module BV = Z3.BitVector
module Bool = Z3.Boolean
module Array = Z3.Z3Array
module Env = Environment
module Constr = Constraint


(** Implements {!Model}. *)

open Core_kernel
open Bap.Std

type sign = Unsigned | Signed

let string_of_sign s =
  match s with
  | Unsigned -> "u"
  | Signed -> "s"

exception NoValue of string

let no_value_msg e m =
  let e_str = Z3.Expr.to_string e in
  let m_str = Z3.Model.to_string m in
  Printf.sprintf "No value for symbol '%s' found in model: %s" e_str m_str

let log ?newline:(newline="\n") msg =
  Printf.printf "[Model] -- %s%s%!" msg newline

let word_of_str s w sign =
  let w_str = Printf.sprintf "%s:%d%s" s w (string_of_sign sign) in
  Word.of_string w_str

let z3_val_of e m =
  match Z3.Model.eval m e true with
  | Some v -> v
  | None -> raise (NoValue (no_value_msg e m))

let word_of_z3_bv bv =
  let bits = Z3.BitVector.get_size (Z3.Expr.get_sort bv) in
  let sign = Unsigned in
  let s = Z3.Expr.to_string bv in
  word_of_str (String.substr_replace_first s ~pattern:"#" ~with_:"0") bits sign

(* get var will actually create a new variable if it can't find the one we're asking for. *)

let val_for_reg r m env =
  let reg_var = Var.create r (Type.imm 64) in
  let reg_value, _ = Environment.get_var env reg_var in
  let v = z3_val_of reg_value m in
  word_of_z3_bv v

let strip_final_digits s =
  let s' = List.rev (String.to_list s) in
  let rec pop_digits l =
    match l with
    | [] -> l
    | x :: xs ->
      begin
        match x with
        | '0' .. '9' -> pop_digits xs
        | _ -> l
      end
    in 
  let s'' = List.rev (pop_digits s') in
  String.of_char_list s''

(*
Target.cpu

get registers names
env has arch
gprs - set of registers - Var

auxv parameer to main
list of pointers 

elf
*)

let reg_names m =
  m |>
  Z3.Model.get_decls |>
  List.map ~f:Z3.FuncDecl.get_name |>
  List.map ~f:Z3.Symbol.to_string |>
  List.filter ~f:(fun s -> String.is_substring_at s 0 "R") |>
  List.map ~f:strip_final_digits


(** [output_gdb] is similar to [print_result] except chews on the model and outputs a gdb script with a 
    breakpoint at the subroutine and fills the appropriate registers *)
(**


create record with all appropriate things

coudl move val_for_reg out

recompile with 01
 (* let decls = Z3.Model.get_const_decls model in *)

 *)

let print_result (solver : Z3.Solver.solver) (status : Z3.Solver.status)
    (goals: Constr.t) (ctx : Z3.context) : unit =
  match status with
  | Z3.Solver.UNSATISFIABLE -> Format.printf "\nUNSAT!\n%!"
  | Z3.Solver.UNKNOWN -> Format.printf "\nUNKNOWN!\n%!"
  | Z3.Solver.SATISFIABLE ->
    Format.printf "\nSAT!\n%!";
    let model = Z3.Solver.get_model solver
                |> Option.value_exn ?here:None ?error:None ?message:None in
    Format.printf "\nModel:\n%s\n%!" (Z3.Model.to_string model);
    let refuted_goals = Constr.get_refuted_goals goals solver ctx in
    Format.printf "\nRefuted goals:\n%!";
    Seq.iter refuted_goals ~f:(fun g ->
        Format.printf "%s\n%!" (Constr.refuted_goal_to_string g model))



let output_gdb (solver : Z3.Solver.solver) (status : Z3.Solver.status)
    (goals: Constr.t) (ctx : Z3.context) (env : Env.t) (func : string) ~filename:(gdb_filename : string) : unit =
    let model = Z3.Solver.get_model solver
            |> Option.value_exn ?here:None ?error:None ?message:None in
    let regs = reg_names model in
    Out_channel.with_file gdb_filename  ~f:(fun t -> 
        Printf.fprintf t "break *%s\n" func; (* The "*" is necessary to break before some slight setup *)
        Printf.fprintf t "start\n";
        List.iter regs ~f:(fun r -> 
              let w = val_for_reg r model env in
              let s = Format.asprintf "set $%s = %a \n" (String.lowercase r) Bap.Std.Word.pp_hex w  in
              Printf.fprintf t "%s" s)     
     )


