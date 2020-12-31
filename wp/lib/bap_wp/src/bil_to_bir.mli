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

   This module provides utilities to translate from a BIL
   {!Bil.t} expression to a BIR subroutine, for which we can
   then invoke {!Precondition.visit_sub} to get the weakest
   precondition.

   This enables using the clean BIL embedded DSL syntax, e.g.

   {[
     Bil.([
         v := src lsr i32 1;
         r := src;
         s := i32 31;
         while_ (var v <> i32 0) [
           r := var r lsl i32 1;
           r := var r lor (var v land i32 1);
           v := var v lsr i32 1;
           s := var s - i32 1;
         ];
         dst := var r lsl var s;
       ]) |> bil_to_sub
   ]}

   As in the BAP documentation, to build subroutines.

*)

open Bap.Std

(** Create a pair of a subroutine with name [__assert_fail] and an
    expression which represents an invocation of that subroutine.

    A subsequent call to {!bil_to_sub} will correctly translate that
    expression to a BIR [call] expression. *)
val mk_assert_fail : unit -> sub term * exp


(** Take a BIL program (a list of statements) and turn it into a
    subroutine. *)
val bil_to_sub : bil -> sub term

(** Take a [sub term] and a type for the term to build a BIL
    function-call *)
val call : sub term -> typ -> Bil.Types.stmt


