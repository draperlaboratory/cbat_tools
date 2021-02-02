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
include Bap.Std
include Cbat_vsa_utils
module MapLattice = Cbat_map_lattice
module Mem = Cbat_ai_memmap
module WordSet = Cbat_clp_set_composite
module Utils = Cbat_vsa_utils

(* The full abstract representation for the value set analysis *)

type wordset = WordSet.t


(* Rename same to equal so that variables as keys to the environment
   are compared ignoring their indices (a peice of BAP metadata).
   TODO: is this right & is this sufficient? (maybe, no)
*)
module VarKey = struct
  include Var
  let equal = same
end

module MemEnv = MapLattice.Make_indexed_val(VarKey)(Mem)
module WordEnv = MapLattice.Make_indexed_val(VarKey)(WordSet)

type t = { memories : MemEnv.t; words : WordEnv.t } [@@deriving bin_io, sexp, compare]

let top : t =
  { memories = MemEnv.top;
    words = WordEnv.top;
  }
let bottom : t =
  { memories = MemEnv.bottom;
    words = WordEnv.bottom;
  }

(* if either the word env or mem env represents the empty set of states
   then this abstract state represents the empty set of states, i.e. bottom.
   Function in this module assume the inputs are canonized in this fashion.
*)
let canonize {memories; words} : t =
  if WordEnv.equal words WordEnv.bottom ||
     MemEnv.equal memories MemEnv.bottom
  then bottom
  else {memories; words}

let equal (e1 : t) e2 : bool =
  MemEnv.equal e1.memories e2.memories &&
  WordEnv.equal e1.words e2.words

(* adds a variable to the memories of the input env *)
let add_memory (e : t) ~(key : var) ~(data : Mem.t) : t =
  (* Note: canonization is unnecessary given the current
     implementation of MemEnv, but it is cheap and better
     to be safe in the case that the implementation changes.
  *)
  canonize
    {memories = MemEnv.add e.memories ~key ~data;
     words = e.words}

(* adds a variable to the words of the input env *)
let add_word (e : t) ~(key : var) ~(data : wordset) : t =
  (* Note: canonization is unnecessary given the current
     implementation of WordEnv, but it is cheap and better
     to be safe in the case that the implementation changes.
  *)
  canonize
    {memories = e.memories;
     words = WordEnv.add e.words ~key ~data}

let find_word (i : WordSet.idx) (env : t) (v : var) : wordset = WordEnv.find i env.words v
let find_memory (i : Mem.idx) (env : t) (v : var) : Mem.t = MemEnv.find i env.memories v

(* Printing *)

let pp ppf (e : t) =
  if equal e bottom then
    Format.fprintf ppf "unreachable"
  else if equal e top then
    Format.fprintf ppf "unknown"
  else begin
    Format.fprintf ppf "@[@[<2>Immediate Variables:@ %a@]@ "
      WordEnv.pp e.words;
    Format.fprintf ppf "@[<2>Memory:@ @ %a@]@]"
      MemEnv.pp e.memories
  end

let join (e1 : t) (e2 : t) : t =
  (* Note: canonization is unnecessary here given the current
     implementation of WordEnv and MemEnv, but it is cheap and better
     to be safe in the case that the implementation changes.
  *)
  canonize
    { memories = MemEnv.join e1.memories e2.memories;
      words = WordEnv.join e1.words e2.words
    }

let widen_join (e1 : t) (e2 : t) : t =
  (* Note: canonization is unnecessary here given the current
     implementation of WordEnv and MemEnv, but it is cheap and better
     to be safe in the case that the implementation changes.
  *)
  canonize
    { memories = MemEnv.widen_join e1.memories e2.memories;
      words = WordEnv.widen_join e1.words e2.words
    }

let meet (e1 : t) (e2 : t) : t =
  (* unlike the other operations, canonization is necessary here
     since the meet of two non-bottom elements can be bottom
  *)
  canonize
    { memories = MemEnv.meet e1.memories e2.memories;
      words = WordEnv.meet e1.words e2.words
    }

let precedes (e1 : t) (e2 : t) : bool =
  MemEnv.precedes e1.memories e2.memories &&
  WordEnv.precedes e1.words e2.words

