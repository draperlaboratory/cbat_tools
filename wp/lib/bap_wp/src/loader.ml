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
open KB.Syntax

let registers_domain : Var.Set.t KB.Domain.t =
  KB.Domain.powerset (module Var) "registers-domain"

let registers : (Theory.Semantics.cls, Var.Set.t) KB.slot =
  KB.Class.property Theory.Semantics.cls
    "referenced-registers" registers_domain
    ~persistent:(KB.Persistent.of_binable (module Var.Set))

let regs_of_insn (target : Theory.Target.t)
    (insn : ('a, 'b) Disasm_expert.Basic.Insn.t) : Var.Set.t =
  Disasm_expert.Basic.Insn.ops insn |>
  Array.fold ~init:Var.Set.empty ~f:(fun regs -> function
      | Op.Imm _ | Op.Fmm _ -> regs
      | Op.Reg r ->
        let reg =
          let (let*) x f = Option.bind x ~f in
          let* var = Theory.Target.var target (Reg.name r) in
          match Theory.Target.unalias target var with
          | None -> Some (Var.reify var)
          | Some origin ->
            let* sub = Theory.Origin.cast_sub origin in
            let reg = Theory.Origin.reg sub in
            let var = Theory.Var.forget reg in
            Some (Var.reify var)
        in
        match reg with
        | None -> regs
        | Some r -> Var.Set.add regs r
    )

(* Computes the registers used in an assembly instruction and stores it in the
   knowledge base. *)
let () =
  KB.promise Theory.Semantics.slot @@ fun label ->
  let* insn = label-->?Disasm_expert.Basic.Insn.slot in
  let* target = Theory.Label.target label in
  let regs = regs_of_insn target insn in
  KB.return @@ KB.Value.put registers Insn.empty regs
