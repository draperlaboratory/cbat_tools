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
open Bap_wp
include Self()

module Comp = Compare
module Pre = Precondition
module Env = Environment
module Constr = Constraint

exception Missing_function of string

let find_func (subs : Sub.t Seq.t) (func : string) : Sub.t =
  match Seq.find ~f:(fun s -> String.equal (Sub.name s) func) subs with
  | None -> raise (Missing_function func)
  | Some f -> f

let update_default_num_unroll (num_unroll : int option) : unit =
  match num_unroll with
  | Some n -> Pre.num_unroll := n
  | None -> ()

let analyze_proj (proj : project) (var_gen : Env.var_gen) (ctx : Z3.context)
    ~func:(func : string) ~inline:(inline : bool) ~post_cond:(post_cond : string)
  : Constr.t =
  let subs = proj |> Project.program |> Term.enum sub_t in
  let main_sub = find_func subs func in
  let env =
    if inline then
      Pre.mk_inline_env ctx var_gen ~subs
    else
      Pre.mk_default_env ctx var_gen ~subs
  in
  let true_constr = Pre.Bool.mk_true ctx |> Constr.mk_goal "true" |> Constr.mk_constr in
  let post =
    if String.(post_cond = "") then
      true_constr
    else
      begin
        (* call visit sub with a dummy postcondition to fill the
           environment with variables *)
        let _, env =
          Pre.visit_sub env true_constr main_sub
        in
        Pre.mk_smtlib2_post env post_cond
      end
  in
  let pre, _ = Pre.visit_sub env post main_sub in
  Format.printf "\nSub:\n%s\nPre:\n%a\n%!"
    (Sub.to_string main_sub) Constr.pp_constr pre;
  pre

let compare_projs (file1: string) (file2 : string)
    (var_gen : Env.var_gen) (ctx : Z3.context) ~func:(func : string)
    ~check_calls:(check_calls : bool) ~inline:(inline : bool) : Constr.t =
  let proj1 = In_channel.with_file file1 ~f:(Project.Io.load) in
  let proj2 = In_channel.with_file file2 ~f:(Project.Io.load) in
  let subs1 = proj1 |> Project.program |> Term.enum sub_t in
  let subs2 = proj2 |> Project.program |> Term.enum sub_t in
  let main_sub1 = find_func subs1 func in
  let main_sub2 = find_func subs2 func in
  (* BUG??: Sub.free_vars only returns a non-empty var set on the SSA form of a sub *)
  let input_vars = Var.Set.union
      (Pre.get_vars main_sub1) (Pre.get_vars main_sub2) in
  let output_vars = Var.Set.union
      (Pre.get_output_vars main_sub1) (Pre.get_output_vars main_sub2) in
  let varset_to_string vs =
    vs |> Var.Set.to_sequence |> Seq.to_list |> List.to_string ~f:Var.to_string in
  debug "Input: %s%!" (varset_to_string input_vars);
  debug "Output: %s%!" (varset_to_string output_vars);
  let env1, env2 =
    if inline then
      Pre.mk_inline_env ctx var_gen ~subs:subs1,
      Pre.mk_inline_env ctx var_gen ~subs:subs2
    else
      Pre.mk_default_env ctx var_gen ~subs:subs1,
      Pre.mk_default_env ctx var_gen ~subs:subs2
  in
  let pre, _ =
    if check_calls then
      Comp.compare_subs_fun ~original:(main_sub1,env1) ~modified:(main_sub2,env2)
    else
      Comp.compare_subs_eq ~input:input_vars ~output:output_vars
        ~original:(main_sub1,env1) ~modified:(main_sub2,env2)
  in
  Printf.printf "\nComparing\n\n%s\nand\n\n%s\n%!"
    (Sub.to_string main_sub1) (Sub.to_string main_sub2);
  pre

let main (file1 : string) (file2 : string)
    ~func:(func : string)
    ~check_calls:(check_calls : bool)
    ~compare:(compare : bool)
    ~inline:(inline : bool)
    ~post_cond:(post_cond : string)
    ~num_unroll:(num_unroll : int option)
    (proj : project) : unit =
  Log.start ~logdir:"/dev/stdout" ();
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let solver = Z3.Solver.mk_simple_solver ctx in
  update_default_num_unroll num_unroll;
  let pre =
    if compare then
      compare_projs file1 file2 var_gen ctx ~func:func ~check_calls:check_calls ~inline:inline
    else
      analyze_proj proj var_gen ctx ~func:func ~inline:inline ~post_cond:post_cond
  in
  let pre' = Constr.eval pre ctx in
  let result = Pre.check solver ctx pre' in
  Pre.print_result solver result

module Cmdline = struct
  open Config

  let file1 = param string "file1" ~doc:"Project file location for first binary"
      ~default:""
  let file2 = param string "file2" ~doc:"Project file location for second binary"
      ~default:""
  let func = param string "function" ~doc:"Function in both binaries to compare"
      ~default:"main"
  let check_calls = param bool "check-calls" ~doc:"Check conservation of function calls"
      ~default:false
  let compare = param bool "compare" ~doc:"Compare the subroutines of two binaries"
      ~default:false
  let inline = param bool "inline" ~doc:"Inline function calls"
      ~default:false
  let post_cond = param string "postcond" ~doc:"Post condition in SMT-LIB format"
      ~default:""
  let num_unroll = param (some int) "num-unroll" ~doc:"Amount of times to unroll each loop"
      ~default:None

  let () = when_ready (fun {get=(!!)} ->
      Project.register_pass' @@
      main !!file1 !!file2
        ~func:!!func
        ~check_calls:!!check_calls
        ~compare:!!compare
        ~inline:!!inline
        ~post_cond:!!post_cond
        ~num_unroll:!!num_unroll
    )

  let () = manpage [
      `S "DESCRIPTION";
      `P
        ("Compute the weakest precondition of a subroutine given a postcondition")
    ]
end
