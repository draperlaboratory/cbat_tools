(***************************************************************************)
(*                                                                         *)
(*  Copyright (C) 2018 The Charles Stark Draper Laboratory, Inc.           *)
(*                                                                         *)
(*  This file is provided under the license found in the LICENSE file in   *)
(*  the top-level directory of this project.                               *)
(*                                                                         *)
(*  This work is funded in part by ONR/NAWC Contract N6833518C0107.  Its   *)
(*  content does not necessarily reflect the position or policy of the US  *)
(*  Government and no official endorsement should be inferred.             *)
(*                                                                         *)
(***************************************************************************)

include Core_kernel
open Bap.Std
open Graphlib.Std
include Self()
include Cbat_vsa_utils

module AI = Cbat_ai_representation
module Utils = Cbat_vsa_utils
module Vsa = Cbat_vsa

let main (sub : string option) (fail_not_impl : bool) (unsound_stack : bool) (show_vsa : bool)
    (proj : project) : project =
  (* turn off to get (very bad) approximations rather than failures
     when an interpretation hasn't been implemented. *)
  Utils.fail_on_not_implemented := fail_not_impl;
  Utils.unsound_stack := unsound_stack;
  let prog = Project.program proj in
  let prog = match sub with
  | Some sname -> Term.filter sub_t prog ~f:(fun s -> sname = Sub.name s)
  | None -> prog in
  let process_sub s =
    let sname = Sub.name s in
    if Option.value ~default:sname sub = sname then begin
      if show_vsa then Format.printf "Analyzing routine %s@." sname;
      let vsa = Vsa.static_graph_vsa [] prog s (Vsa.init_sol s) in
      Term.concat_map blk_t s ~f:begin fun b ->
        let bid = Term.tid b in
        let vsa_res = Solution.get vsa bid in
        let vsa_res' = Vsa.denote_defs b vsa_res in
        if show_vsa then Format.printf
            "%a@ @[Precondition:@ %a@]@ @[Postcondition:@ %a@]@."
            Tid.pp (Term.tid b)
            AI.pp vsa_res
            AI.pp vsa_res';
        [Term.set_attr b Cbat_vsa.precond vsa_res]
      end end
    else s in
  Term.map sub_t prog ~f:process_sub |>
  Project.with_program proj

module Cmdline = struct
  open Config
  let sub = param (some string) "sub" ~doc:"Name of subroutine to analyze"
  let keep_trying = flag "keep-trying"
      ~doc:"When this flag is present, uses broad approximations for unimplemented code"
  let unsound_stack = flag "unsound-stack"
      ~doc:"When this flag is present, uses an unsound initial value of 0 for RSP"
  let show_vsa = param bool "show-vsa" ~default:true
      ~doc:"Whether to print the output of the VSA pass on the command line"

  let () = when_ready (fun {get=(!!)} ->
      Project.register_pass (main !!sub (not !!keep_trying) !!unsound_stack !!show_vsa))

  let () = manpage [
      `S "DESCRIPTION";
      `P
        "Performs value-set analysis. This helps make control flow
    explicit as well as providing information about the possible
    values of program variables"
    ]
end

