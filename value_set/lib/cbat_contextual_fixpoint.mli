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

open Graphlib.Std



(** An extension of the BAP fixpoint function that supports context-sensitive
    analysis.
*)
val fixpoint : (module Graph with type t = 'c
                              and type node = 'n) ->
  ?steps:int -> ?start:'n -> ?rev:bool ->
  ?step:(int -> 'n -> 'd -> 'd -> 'd) ->
  init:('n,'d) Solution.t ->
  equal:('d -> 'd -> bool) ->
  merge:('d -> 'd -> 'd) ->
  f:(source:'n -> 'd -> target:'n -> 'd) -> 'c -> ('n,'d) Solution.t
