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

open !Core
open Bap.Std
open Graphlib.Std

module Constr = Constraint
module Expr = Z3.Expr
module Bool = Z3.Boolean
module BV = Z3.BitVector
module Model = Z3.Model
module Solver = Z3.Solver

module Node = Graphs.Ir.Node
module Edge = Graphs.Ir.Edge
module NodeSet = Graphs.Ir.Node.Set
module EdgeSet = Graphs.Ir.Edge.Set

let add_edges (s : EdgeSet.t) (es : Edge.t list) : EdgeSet.t =
  List.fold es ~f:EdgeSet.add ~init:s

let jmps_of_blk (b : Blk.t) : Jmp.t seq =
  Term.enum jmp_t b

let jmps_of_sub (s : Sub.t) : Jmp.t seq =
  Term.enum blk_t s |> Seq.map ~f:jmps_of_blk |> Seq.concat

let filter_path (p : Constr.path) (jmps : Jmp.t seq) : Constr.path =
  Jmp.Map.filter_keys p ~f:(fun k -> Seq.mem jmps k ~equal:Jmp.equal)

let pick_edges (e1 : Edge.t) (e2 : Edge.t) (path : Constr.path) : Edge.t list =
  let find e = Jmp.Map.find path (Edge.jmp e) in
  let branches_taken, true_edge, false_edge =
    match find e1, find e2 with
    | Some bs, None -> bs, e1, e2
    | None, Some bs -> bs, e2, e1
    | _, _ -> failwith "expected one guarded and one fallthrough edge"
  in
  match branches_taken with
  | Both -> [true_edge; false_edge]
  | Only b -> if b then [true_edge] else [false_edge]

let get_start_node (sub : Sub.t) : Node.t =
  sub |> Term.enum blk_t |> Seq.hd_exn |> Node.create

let get_taken_edges (sub : Sub.t) (path : Constr.path) : EdgeSet.t =
  let cfg = Sub.to_cfg sub in
  let rec walk (worklist : Node.t list) (seen : NodeSet.t) (acc : EdgeSet.t) : EdgeSet.t =
    match worklist with
    | [] -> acc
    | curr_node :: worklist' ->
       if NodeSet.mem seen curr_node then
         walk worklist' seen acc
       else
         let seen' = NodeSet.add seen curr_node in
         let out_edges = Node.outputs curr_node cfg |> Seq.to_list in
         match out_edges with
         | [] -> walk worklist' seen' acc
         | [e] -> walk (Edge.dst e :: worklist') seen' (EdgeSet.add acc e)
         | [e1; e2] ->
            let taken_edges = pick_edges e1 e2 path in
            let taken_dests = List.map taken_edges ~f:Edge.dst in
            walk (taken_dests @ worklist') seen' (add_edges acc taken_edges)
         | _ -> failwith (Printf.sprintf
                            "unexpected number of edges: %d" (List.length out_edges))
  in
  walk [get_start_node sub] NodeSet.empty EdgeSet.empty

let taken_edges_of_refuted_goal (rg : Constr.refuted_goal) (sub1 : Sub.t) (sub2 : Sub.t) :
      EdgeSet.t * EdgeSet.t =
  let path_combined = Constr.path_of_refuted_goal rg in
  let taken_edges_of_sub (s : Sub.t) : EdgeSet.t =
    let p = filter_path path_combined (jmps_of_sub s) in
    get_taken_edges s p
  in
  (taken_edges_of_sub sub1, taken_edges_of_sub sub2)

let left_justify : string -> string =
  String.concat_map ~f:(fun c -> if Char.equal c '\n' then "\\l" else Char.to_string c)

let write_highlighted_cfg (sub : Sub.t) ~(highlight : EdgeSet.t) ~(filename : string) : unit =
  let string_of_node node =
    sprintf "\"\\%s\"" @@ Blk.to_string @@ Node.label node |> left_justify
  in
  let node_attrs _ = [`Shape `Box] in
  let edge_attrs e = if EdgeSet.mem highlight e then [`Penwidth 5.0] else [`Penwidth 1.0; `Style `Dashed] in
  Graphlib.to_dot (module Graphs.Ir)
    ~string_of_node ~node_attrs ~edge_attrs ~filename @@ Sub.to_cfg sub

let pp_cfg_path_fst_refuted_goal
      (rgs : Constr.refuted_goal seq)
      ~(f : Sub.t) ~(g : Sub.t)
      ~(f_out : string) ~(g_out : string) : unit =
  match Seq.hd rgs with
  | None -> print_endline "no refuted goals"
  | Some rg ->
     let es1, es2 = taken_edges_of_refuted_goal rg f g in
     write_highlighted_cfg f ~highlight:es1 ~filename:f_out;
     write_highlighted_cfg g ~highlight:es2 ~filename:g_out
