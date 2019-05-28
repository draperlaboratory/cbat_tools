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

open Core_kernel.Std
open Graphlib.Std

let sol_map ~(f : 'd -> 'a) s : ('n, 'a) Solution.t =
  let default = Solution.default s |> f in
  Solution.derive s ~f:(fun _ d -> Some (f d)) default

type ('n,'d) ctxed = Dep of ('n -> 'd) | Const of 'd
type ('n,'d) ctx_sol = ('n, ('n,'d) ctxed) Solution.t

let ctx_id ~source:_ ~target:_ x = x

let app_ctxed : ('n,'d) ctxed -> 'n -> 'd = function
  | Dep f -> f
  | Const c -> fun _ -> c

let ctxed_merge merge
    (d1: ('n,'d) ctxed)
    (d2 : ('n,'d) ctxed) : ('n,'d) ctxed = Dep (fun target ->
    let d1_v = app_ctxed d1 target in
    let d2_v = app_ctxed d2 target in
    merge d1_v d2_v)

let ctxed_equal equal
    (d1 : ('n,'d) ctxed)
    (d2 : ('n,'d) ctxed) : bool = match d1, d2 with
  | Const d1_v, Const d2_v -> equal d1_v d2_v
  | Dep _, _
  | _, Dep _ -> false

let ctxed_init init : ('n,'d) ctx_sol =
  Solution.derive init ~f:(fun _ d -> Some (Const d)) (Const (Solution.default init))

let ctxed_step step (i : int) n
    (d : ('n,'d) ctxed)
    (d' : ('n,'d) ctxed) : ('n,'d) ctxed =
  let d_v = app_ctxed d n in
  let d'_v = app_ctxed d' n in
  Const (step i n d_v d'_v)


let fixpoint (type g n d)
    (module G : Graph with type t = g and type node = n)
    ?steps ?start ?(rev=false) ?step
    ~init ~equal ~merge ~f g : (n,d) Solution.t =
  let step = Option.value ~default:(fun _ _ _ x -> x) step in
  let f n d =
    let d_v = app_ctxed d n in
    let f_app = f ~source:n d_v in
    Dep (fun target -> f_app ~target) in
  let compute_val (n : n) (d : (n,d) ctxed) : d option = Some (app_ctxed d n) in
  Solution.derive ~f:compute_val begin
    Graphlib.fixpoint (module G) ?steps ?start ~rev
      ~step:(ctxed_step step)
      ~init:(ctxed_init init)
      ~equal:(ctxed_equal equal)
      ~merge:(ctxed_merge merge) ~f g
  end (Solution.default init)

