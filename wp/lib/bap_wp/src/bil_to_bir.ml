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
   [x := e], [while_ e b] and [if_ e a b] are for now.

*)

open !Core_kernel
open Bap.Std

let mk_assert_fail () : Sub.t * Exp.t =
  let call_tid = Tid.create () in
  Tid.set_name call_tid "__assert_fail";
  let call_sub = Sub.create ~tid:call_tid ~name:"__assert_fail" () in
  call_sub, Bil.unknown (Tid.to_string call_tid) reg64_t

let rec stmt_to_blks
    (stmt : Bil.Types.stmt)
    (sub : Sub.Builder.t)
    (tail_blk : Blk.Builder.t)
  : Sub.Builder.t * Blk.Builder.t =
  match stmt with
  | Bil.Types.Move (x, e) -> mk_move x e sub tail_blk
  | Bil.Types.If (e, ls, rs) -> mk_if e ls rs sub tail_blk
  | Bil.Types.While (e, ss) -> mk_while e ss sub tail_blk
  | Bil.Types.Jmp e -> mk_jmp e sub tail_blk
  (* We currently don't handle any of these cases. *)
  | Bil.Types.Special _ -> assert false
  | Bil.Types.CpuExn _ -> assert false

and mk_move (x : Var.t) (e : Exp.t) (sub : Sub.Builder.t) (blk : Blk.Builder.t)
  : Sub.Builder.t * Blk.Builder.t  =
  Blk.Builder.add_def blk (Def.create x e);
  sub, blk

and mk_if
    (e : Exp.t)
    (ls : stmt list)
    (rs : stmt list)
    (sub : Sub.Builder.t)
    (blk : Blk.Builder.t)
  : Sub.Builder.t * Blk.Builder.t =
  let tid_l = Tid.create () in
  let tid_r = Tid.create () in
  (* We pass along the sub builder, to add all required blocks in both branches *)
  let sub, blk_r = bil_to_blks rs sub (Blk.Builder.create ~tid:tid_r ()) in
  let sub, blk_l = bil_to_blks ls sub (Blk.Builder.create ~tid:tid_l ()) in
  Blk.Builder.add_jmp blk (Jmp.create ~cond:e (Goto (Label.direct tid_l)));
  Blk.Builder.add_jmp blk (Jmp.create (Goto (Label.direct tid_r)));
  let old_blk = Blk.Builder.result blk in
  let merge_tid = Tid.create () in
  let merge_blk = Blk.Builder.create ~tid:merge_tid () in
  let lab = Label.direct merge_tid in
  Blk.Builder.add_jmp blk_l (Jmp.create (Goto lab));
  let lhs_blk = Blk.Builder.result blk_l in
  Blk.Builder.add_jmp blk_r (Jmp.create (Goto lab));
  let rhs_blk = Blk.Builder.result blk_r in
  Sub.Builder.add_blk sub old_blk;
  Sub.Builder.add_blk sub rhs_blk;
  Sub.Builder.add_blk sub lhs_blk;
  sub, merge_blk

and mk_while (e : Exp.t) (ss : stmt list) (sub : Sub.Builder.t) (blk : Blk.Builder.t)
  : Sub.Builder.t * Blk.Builder.t =
  let exit_tid = Tid.create () in
  let entry_tid = Tid.create () in
  let body_tid = Tid.create () in
  let exit_block = Blk.Builder.create ~tid:exit_tid () in
  let entry_block = Blk.Builder.create ~tid:entry_tid () in
  let body_block = Blk.Builder.create ~tid:body_tid () in
  Blk.Builder.add_jmp blk (Jmp.create (Goto (Label.direct entry_tid)));
  Blk.Builder.add_jmp entry_block
    (Jmp.create ~cond:(Bil.lnot e) (Goto (Label.direct exit_tid)));
  Blk.Builder.add_jmp entry_block
    (Jmp.create (Goto (Label.direct body_tid)));
  let sub_loop, blk_loop = bil_to_blks ss sub body_block in
  Blk.Builder.add_jmp blk_loop
    (Jmp.create (Goto (Label.direct entry_tid)));
  Sub.Builder.add_blk sub (Blk.Builder.result blk);
  Sub.Builder.add_blk sub (Blk.Builder.result entry_block);
  Sub.Builder.add_blk sub_loop (Blk.Builder.result blk_loop);
  sub_loop, exit_block

(* This is a huge hack to enable calling "special" functions with chosen names
   and [tid]s. *)
and mk_jmp (e : Exp.t) (sub : Sub.Builder.t) (blk : Blk.Builder.t)
  : Sub.Builder.t * Blk.Builder.t =
  match e with
  | Bil.Unknown (tid_s, _) ->
    let call_tid = Tid.from_string_exn tid_s in
    Blk.Builder.add_jmp blk
      (Jmp.create (Call (Call.create ~target:(Label.direct call_tid) ())));
    sub, blk
  | _ ->
    Blk.Builder.add_jmp blk
      (Jmp.create (Goto (Label.indirect e)));
    sub, blk

and bil_to_blks
    (stmts : Bil.t)
    (sub : Sub.Builder.t)
    (tail_blk : Blk.Builder.t)
  : Sub.Builder.t * Blk.Builder.t =
  match stmts with
  | [] -> sub, tail_blk
  | s::ss ->
    let sub', tail_blk' = stmt_to_blks s sub tail_blk in
    bil_to_blks ss sub' tail_blk'

let bil_to_sub (stmts : Bil.t) : sub term =
  let head_tid = Tid.create () in
  let new_sub = Sub.Builder.create () in
  let new_blk = Blk.Builder.create ~tid:head_tid () in
  let sub, blk = bil_to_blks stmts new_sub new_blk in
  (* Add the last "trailing" block to the subroutine *)
  Sub.Builder.add_blk sub (Blk.Builder.result blk);
  let res_sub = Sub.Builder.result sub in
  (* We need to shuffle things around so the the head block is first *)
  let hd_blk = Option.value_exn (Term.find blk_t res_sub head_tid) in
  let res_sub = Term.remove blk_t res_sub head_tid in
  let res_sub = Term.prepend blk_t res_sub hd_blk in
  res_sub
