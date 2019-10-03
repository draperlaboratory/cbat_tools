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

let missing_func_msg (func : string) : string =
  Format.sprintf "Missing function: %s is not in binary." func

let diff_arch_msg (arch1 : Arch.t) (arch2 : Arch.t) : string =
  Format.sprintf "Binaries are of two different architectures: %s vs %s"
    (Arch.to_string arch1) (Arch.to_string arch2)

let find_func_err (subs : Sub.t Seq.t) (func : string) : Sub.t =
  match Seq.find ~f:(fun s -> String.equal (Sub.name s) func) subs with
  | None -> failwith (missing_func_msg func)
  | Some f -> f

(* Not efficient, but easier to read *)
let find_func_in_one_of (f : string) ~to_find:(to_find : Sub.t Seq.t)
    ~to_check:(to_check : Sub.t Seq.t) : Sub.t list =
  match Seq.find ~f:(fun s -> String.equal (Sub.name s) f) to_find with
  | None -> if Option.is_some (Seq.find ~f:(fun s -> String.equal (Sub.name s) f) to_check)
    then []
    else failwith (missing_func_msg f)
  | Some f -> [f]

let update_default_num_unroll (num_unroll : int option) : unit =
  match num_unroll with
  | Some n -> Pre.num_unroll := n
  | None -> ()

let has_inline_funcs (to_inline : string list) : bool =
  not (List.is_empty to_inline)

let find_inline_funcs (inline_funcs : string list) ~to_find:(to_find : Sub.t Seq.t)
    ~to_check:(to_check : Sub.t Seq.t) : Sub.t Seq.t =
  if List.is_empty inline_funcs then
    to_find
  else
    inline_funcs
    |> List.map ~f:(find_func_in_one_of ~to_find ~to_check)
    |> List.concat
    |> Seq.of_list

let varset_to_string (vs : Var.Set.t) : string =
  vs
  |> Var.Set.to_sequence
  |> Seq.to_list
  |> List.to_string ~f:Var.to_string

let analyze_proj (proj : project) (var_gen : Env.var_gen) (ctx : Z3.context)
    ~func:(func : string)
    ~inline:(inline : bool)
    ~to_inline:(to_inline : string list)
    ~post_cond:(post_cond : string)
  : Constr.t * Env.t * Env.t =
  let arch = Project.arch proj in
  let subs = proj |> Project.program |> Term.enum sub_t in
  let main_sub = find_func_err subs func in
  let env =
    if inline || has_inline_funcs to_inline then
      let to_inline =
        if List.is_empty to_inline then
          subs
        else
          to_inline
          |> List.map ~f:(find_func_err subs)
          |> Seq.of_list
      in
      Pre.mk_inline_env ctx var_gen ~subs ~arch ~to_inline:to_inline
    else
      Pre.mk_default_env ctx var_gen ~subs ~arch
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
  let pre, env' = Pre.visit_sub env post main_sub in
  Format.printf "\nSub:\n%s\nPre:\n%a\n%!"
    (Sub.to_string main_sub) Constr.pp_constr pre;
  (pre, env', env)

let compare_projs (proj : project) (file1: string) (file2 : string)
    (var_gen : Env.var_gen) (ctx : Z3.context)
    ~func:(func : string)
    ~check_calls:(check_calls : bool)
    ~inline:(inline : bool)
    ~to_inline:(to_inline : string list)
    ~output_vars:(output_vars : string list)
  : Constr.t * Env.t * Env.t =
  let prog1 = Program.Io.read file1 in
  let prog2 = Program.Io.read file2 in
  (* Currently using the dummy binary's project to determine the architecture
     until we discover a better way of determining the architecture from a program. *)
  let arch = Project.arch proj in
  let subs1 = Term.enum sub_t prog1 in
  let subs2 = Term.enum sub_t prog2 in
  let main_sub1 = find_func_err subs1 func in
  let main_sub2 = find_func_err subs2 func in
  let env1, env2 =
    if inline || has_inline_funcs to_inline then
      let to_inline1 = find_inline_funcs to_inline ~to_find:subs1 ~to_check:subs2 in
      let to_inline2 = find_inline_funcs to_inline ~to_find:subs2 ~to_check:subs1 in
      Pre.mk_inline_env ctx var_gen ~subs:subs1 ~arch:arch ~to_inline:to_inline1,
      Pre.mk_inline_env ctx var_gen ~subs:subs2 ~arch:arch ~to_inline:to_inline2
    else
      Pre.mk_default_env ctx var_gen ~subs:subs1 ~arch:arch,
      Pre.mk_default_env ctx var_gen ~subs:subs2 ~arch:arch
  in
  let pre, env1, env2 =
    if check_calls then
      Comp.compare_subs_fun ~original:(main_sub1,env1) ~modified:(main_sub2,env2)
    else
      begin
        let output_vars = Var.Set.union
            (Pre.get_output_vars main_sub1 output_vars)
            (Pre.get_output_vars main_sub2 output_vars) in
        let input_vars = Var.Set.union
            (Pre.get_vars main_sub1) (Pre.get_vars main_sub2) in
        debug "Input: %s%!" (varset_to_string input_vars);
        debug "Output: %s%!" (varset_to_string output_vars);
        Comp.compare_subs_eq ~input:input_vars ~output:output_vars
          ~original:(main_sub1,env1) ~modified:(main_sub2,env2)
      end
  in
  Format.printf "\nComparing\n\n%s\nand\n\n%s\n%!"
    (Sub.to_string main_sub1) (Sub.to_string main_sub2);
  (pre, env1, env2)

let main (file1 : string) (file2 : string)
    ~func:(func : string)
    ~check_calls:(check_calls : bool)
    ~compare:(compare : bool)
    ~inline:(inline : bool)
    ~to_inline:(to_inline : string list)
    ~post_cond:(post_cond : string)
    ~num_unroll:(num_unroll : int option)
    ~output_vars:(output_vars : string list)
    ~gdb_filename:(gdb_filename : string option)
    (proj : project) : unit =
  Log.start ~logdir:"/dev/stdout" ();
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let solver = Z3.Solver.mk_simple_solver ctx in
  update_default_num_unroll num_unroll;
  let has_files_to_compare = String.(file1 <> "" && file2 <> "") in
  let pre, env1, env2 =
    if compare || has_files_to_compare then
      compare_projs proj file1 file2 var_gen ctx ~func ~check_calls ~inline ~to_inline ~output_vars
    else
      analyze_proj proj var_gen ctx ~func ~inline ~to_inline ~post_cond
  in
  let result = Pre.check solver ctx pre in
  let () = match gdb_filename with
    | None -> ()
    | Some f ->
      Printf.printf "Dumping gdb script to file: %s\n" f;
      Output.output_gdb solver result env2 ~func:func ~filename:f in
  Output.print_result solver result pre ~orig:env1 ~modif:env2


module Cmdline = struct
  open Config

  let compare = param bool "compare" ~as_flag:true ~default:false
      ~doc:"Determines whether to analyze a single function or compare the same \
            function across two binaries. If enabled, project files must be specified \
            with the `file1' and `file2' options."

  let file1 = param string "file1" ~default:""
      ~doc:"Project file location of the first binary for comparative analysis, \
            which can be generated via the save-project plugin. If both `file1' and \
            `file2' are specified, wp will automatically run the comparative analysis."

  let file2 = param string "file2" ~default:""
      ~doc:"Project file location of the second binary for comparative analysis, \
            which can be generated via the save-project plugin. If both `file1' and \
            `file2' are specified, wp will automatically run the comparative analysis."

  let func = param string "function" ~default:"main"
      ~doc:"Function to run the wp analysis on. `main' by default. If the function \
            cannot be found in the binary or both binaries in the comparison \
            case, wp analysis should fail."

  let check_calls = param bool "check-calls" ~as_flag:true ~default:false
      ~doc:"If set, compares which subroutines are invoked in the body of the \
            function. Otherwise, compares the return values computed in the function \
            body."

  let inline = param bool "inline" ~as_flag:true ~default:false
      ~doc:"Inline function calls. Use in conjunction with `inline-funcs' to \
            specify which functions should be replaced by their bodies for purposes \
            of analysis. If not set, function summaries are used at function call \
            time."

  let to_inline = param (list string) "inline-funcs"
      ~doc:"List of functions to inline separated by `,'. By default, if `inline' \
            is set without specifying `inline-funcs', all functions in the binary \
            will be inlined."
      ~default:[]

  let post_cond = param string "postcond" ~default:""
      ~doc:"Post condition in SMT-LIB format used when analyzing a single binary. \
            If no post condition is specified, a trivial post condition (`true') \
            will be used."

  let num_unroll = param (some int) "num-unroll"
      ~doc:"Amount of times to unroll each loop. By default, wp will unroll each \
            loop 5 times."
      ~default:None

  let output_vars = param (list string) "output-vars" ~default:["RAX"; "EAX"]
      ~doc:"List of output variables to compare separated by `,' given the same \
            input variables in the case of a comparative analysis. Defaults to `RAX,EAX' \
            which are the 64- and 32-bit output registers for x86."
  let gdb_filename = param (some string) "gdb-filename" ~doc:"Output gdb script file for counterexample"
      ~default:None


  let () = when_ready (fun {get=(!!)} ->
      Project.register_pass' @@
      main !!file1 !!file2
        ~func:!!func
        ~check_calls:!!check_calls
        ~compare:!!compare
        ~inline:!!inline
        ~to_inline:!!to_inline
        ~post_cond:!!post_cond
        ~num_unroll:!!num_unroll
        ~output_vars:!!output_vars
        ~gdb_filename:!!gdb_filename
    )

  let () = manpage [
      `S "DESCRIPTION";
      `P "Computes the weakest precondition of a subroutine given a postcondition."
    ]
end
