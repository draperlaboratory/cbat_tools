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

open Core_kernel
open Bap.Std
open Graphlib.Std

let back_edge = Value.Tag.register (module Unit)
    ~name:"CFG back edge"
    ~uuid:"b1688341-ee2c-4d3a-8dd8-2eba369dd4bb"

module G = Graphs.Ir

let clear_back_edges (s : sub term) : sub term =
  Term.map blk_t s ~f:begin fun blk ->
    Term.map jmp_t blk ~f:begin fun jmp ->
      Term.del_attr jmp back_edge
    end
  end

let label_back_edges (sub : sub term) : sub term =
  let graph = Sub.to_cfg (clear_back_edges sub) in
  let enter_edge k e s = match k with
    | `Back ->
      let jmp = G.Edge.jmp e in
      let jmp' = Term.set_attr jmp back_edge () in
      Term.map blk_t s ~f:begin fun blk ->
        Term.update jmp_t blk jmp'
      end
    | _ -> s
  in
  Graphlib.depth_first_search (module G) ~enter_edge graph ~init:sub
