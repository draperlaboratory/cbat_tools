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

(* Utility functions specific to this project but not associated with
   any particular piece of functionality.
 *)

exception NotImplemented of string

(* When true, the analysis fails whenever it encounters a denotation
   that isn't implemented yet. When false, the analysis proceeds with
   a (very) conservative approximation.
 *)
let fail_on_not_implemented = ref true

(* call as a placeholder where a piece of code has not been written yet.
   An optional argument, top, is for a conservative approximation of
   the desired result, where appropriate.
 *)
let not_implemented ?(top : 'a option) component : 'a = match top with
  | None -> raise (NotImplemented component)
  | Some tp -> if !fail_on_not_implemented
    then raise (NotImplemented component)
    else tp

(* When set to true, the analysis is UNSOUND in general. Note that the
   analysis will print a note if it might be unsound (i.e. no note
   implies soundness, but not vice versa).
   When true, the analysis will assume that loads and stores are done on
   memory bounds, i.e. bytes are only assigned to as a part of a fixed,
   contiguous, word-sized group.
*)
let unsound_assume_memory_alignment = ref true

(* When set to true, the analysis is UNSOUND. Specifically, any values derived
   from RSP will be incorrect. However, so long as these values never overlap
   other pointers, the values they point to should be correct.
   TODO: implement the "value-set" part of the analysis to make this more robust
*)
let unsound_stack = ref false


(* Determines the maximum edge multiple that the pass can produce.
*)
let max_edge_explosion = ref 10

(* Determines the maximum number of elements in an exact set abstraction *)
let fin_set_size = ref 10

(* implements integer division rounding upwards *)
let cdiv (x : int) (y : int) : int = (x - 1)/y + 1

open !Core_kernel.Std
open Bap.Std

let exn_on_err : ('a, Type.error) Result.t -> 'a = function
  | Ok e -> e
  | Error e -> raise (Type.Error.T e)

let rotate_list (l : 'a list) : 'a list =
  let l_r = List.rev l in
  match l_r with
  | [] -> []
  | hd::tl -> hd::(List.rev tl)
