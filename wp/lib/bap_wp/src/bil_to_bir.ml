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

(**
   This module allows creating simple subroutines based on the
   BIL quasi-quoting notations.

   [example]

   Note that not all BIL instructions are supported, only
   [x := e], [while_ e b] and [if_ e a b] are for now. *)

open !Core_kernel
open Bap.Std


let mk_assert_fail () : Sub.t * Exp.t =
  let call_tid = Tid.create () in
  Tid.set_name call_tid "__assert_fail";
  let call_sub = Sub.create ~tid:call_tid ~name:"__assert_fail" () in
  call_sub, Bil.unknown (Tid.to_string call_tid) reg64_t


let rec stmt_to_blks (stmt : Bil.Types.stmt)
    (sub : Sub.Builder.t)
    (tail_blk : Blk.Builder.t)
  : Sub.Builder.t * Blk.Builder.t =
  match stmt with
  | Bil.Types.Move (x, e) ->
    Blk.Builder.add_def tail_blk (Def.create x e);
    sub, tail_blk
  | Bil.Types.If (e, ls, rs) ->
    let tid_l = Tid.create () in
    let tid_r = Tid.create () in
    let sub_l, blk_l = bil_to_blks ls sub (Blk.Builder.create ~tid:tid_l ()) in
    (* We pass along the sub builder, to add all required blocks in both branches *)
    let sub_r, blk_r = bil_to_blks rs sub_l (Blk.Builder.create ~tid:tid_r ()) in
    Blk.Builder.add_jmp tail_blk (Jmp.create ~cond:e (Goto (Label.direct tid_l)));
    Blk.Builder.add_jmp tail_blk (Jmp.create (Goto (Label.direct tid_r)));
    let old_blk = Blk.Builder.result tail_blk in
    Sub.Builder.add_blk sub_r old_blk;
    let merge_tid = Tid.create () in
    let merge_blk = Blk.Builder.create ~tid:merge_tid () in
    let lab = Label.direct merge_tid in
    Blk.Builder.add_jmp blk_l (Jmp.create (Goto lab));
    let lhs_blk = Blk.Builder.result blk_l in
    Sub.Builder.add_blk sub_r lhs_blk;
    Blk.Builder.add_jmp blk_r (Jmp.create (Goto lab));
    let rhs_blk = Blk.Builder.result blk_r in
    Sub.Builder.add_blk sub_r rhs_blk;
    sub_r, merge_blk

  | Bil.Types.While (e, ss) ->
    let exit_tid = Tid.create () in
    let entry_tid = Tid.create () in
    let body_tid = Tid.create () in
    let exit_block = Blk.Builder.create ~tid:exit_tid () in
    let entry_block = Blk.Builder.create ~tid:entry_tid () in
    let body_block = Blk.Builder.create ~tid:body_tid () in
    Blk.Builder.add_jmp tail_blk (Jmp.create (Goto (Label.direct entry_tid)));
    Sub.Builder.add_blk sub (Blk.Builder.result tail_blk);
    Blk.Builder.add_jmp entry_block
      (Jmp.create ~cond:(Bil.lnot e) (Goto (Label.direct exit_tid)));
    Blk.Builder.add_jmp entry_block
      (Jmp.create (Goto (Label.direct body_tid)));
    Sub.Builder.add_blk sub (Blk.Builder.result entry_block);
    let sub_loop, blk_loop = bil_to_blks ss sub body_block in
    Blk.Builder.add_jmp blk_loop
      (Jmp.create (Goto (Label.direct entry_tid)));
    Sub.Builder.add_blk sub_loop (Blk.Builder.result blk_loop);
    sub_loop, exit_block

  | Bil.Types.Jmp e ->
    begin
      match e with
      (* This is a huge hack to enable calling "special" functions with chosen names
         and [tid]s
      *)
      | Bil.Unknown (tid_s, _) ->
        let call_tid = Tid.from_string_exn tid_s in
        Tid.set_name call_tid "__assert_fail";
        Blk.Builder.add_jmp tail_blk
          (Jmp.create (Call (Call.create ~target:(Label.direct call_tid) ())));
        sub, tail_blk
      | _ ->
        Blk.Builder.add_jmp tail_blk
          (Jmp.create (Goto (Label.indirect e)));
        sub, tail_blk
    end

  (* We currently don't handle any of these cases *)

  | Bil.Types.Special _ -> assert false

  | Bil.Types.CpuExn _ -> assert false

and bil_to_blks (stmts : Bil.t)
    (sub : Sub.Builder.t)
    (tail_blk : Blk.Builder.t)
  : Sub.Builder.t * Blk.Builder.t =
  match stmts with
  | [] -> sub, tail_blk
  | s::ss ->
    let sub', tail_blk' = stmt_to_blks s sub tail_blk in
    bil_to_blks ss sub' tail_blk'

let bil_to_sub (stmts : Bil.t) : sub term =
  let new_sub = Sub.Builder.create () in
  let new_blk = Blk.Builder.create () in
  let sub, blk = bil_to_blks stmts new_sub new_blk in
  Sub.Builder.add_blk sub (Blk.Builder.result blk);
  Sub.Builder.result sub
