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

open !Core_kernel
open Bap.Std

include Self()

module Expr = Z3.Expr

(* The environment for computing the semantics of an instruction *)
module EnvMap = Var.Map
module TidMap = Tid.Map
module StringMap = String.Map

type z3_expr = Expr.expr

type var_gen = int ref

type t = {
  ctx : Z3.context;
  var_gen : var_gen;
  subs : Sub.t Seq.t;
  var_map : z3_expr EnvMap.t;
  precond_map : z3_expr TidMap.t;
  fun_name_tid : Tid.t StringMap.t;
  call_map : string TidMap.t;
  sub_handler : fun_spec TidMap.t;
  jmp_handler : jmp_spec;
  int_handler : int_spec;
  loop_handler : loop_handler;
  exp_conds : exp_cond list
}

and fun_spec_type =
  | Summary of (t -> z3_expr -> Tid.t -> z3_expr)
  | Inline

and fun_spec = {
  spec_name : string;
  spec : fun_spec_type
}

and jmp_spec = t -> z3_expr -> Tid.t -> Jmp.t -> z3_expr option

and int_spec = t -> z3_expr -> int -> z3_expr

and loop_handler = {
  (* Updates the environment with the preconditions computed by
     the loop handling procedure for the appropriate blocks *)
  handle : t -> z3_expr -> start:Graphs.Ir.Node.t -> Graphs.Ir.t -> t
}

and cond_type = Verify of z3_expr | Assume of z3_expr

and exp_cond = t -> Bap.Std.Exp.t -> cond_type option

let mk_ctx () : Z3.context = Z3.mk_context []

let mk_var_gen () : int ref = ref 0

let init_fun_name (subs : Sub.t Seq.t) : Tid.t StringMap.t =
  Seq.fold subs ~init:StringMap.empty
    ~f:(fun map sub ->
        StringMap.set map ~key:(Sub.name sub) ~data:(Term.tid sub))

let get_fresh ?name:(n = "fresh_") (var_seed : var_gen) : string =
  incr var_seed;
  n ^ (string_of_int !var_seed)

let init_call_map (var_gen : var_gen) (subs : Sub.t Seq.t) : string TidMap.t =
  Seq.fold subs ~init:TidMap.empty
    ~f:(fun map sub ->
        let is_called = get_fresh ~name:("called_" ^ (Sub.name sub)) var_gen in
        TidMap.set map ~key:(Term.tid sub) ~data:is_called)

let init_sub_handler (subs : Sub.t Seq.t)
    ~specs:(specs : (Sub.t -> fun_spec option) list)
    ~default_spec:(default_spec : fun_spec) : fun_spec TidMap.t =
  Seq.fold subs ~init:TidMap.empty
    ~f:(fun map sub ->
        let spec = List.find_map specs ~f:(fun creator -> creator sub)
                   |> Option.value ~default:default_spec in
        info "%s: %s%!" (Sub.name sub) spec.spec_name;
        TidMap.set map ~key:(Term.tid sub) ~data:spec)

(* FIXME: this is something of a hack: we use a function ref as a
   place holder for the WP transform for subroutines, which itself is
   needed in the loop handler defined in the environment.

   It will be substituted by the actual visit_sub function at the
   point of definition. This is used to simulate "open recursion".  *)
let wp_rec_call :
  (t -> z3_expr -> start:Graphs.Ir.Node.t -> Graphs.Ir.t -> t) ref =
  ref (fun _ _ ~start:_ _ -> assert false)

let init_loop_unfold (num_unroll : int) : loop_handler =
  {
    handle =
      let module Node = Graphs.Ir.Node in
      let depth : (Blk.t, int) Hashtbl.t = Hashtbl.create (module Blk) in
      let find_depth node = Hashtbl.find_or_add depth (Node.label node)
          ~default:(fun () -> num_unroll)
      in
      let decr_depth node =
        Hashtbl.update depth (Node.label node) ~f:(function None -> assert false | Some n -> n-1)
      in
      let rec unroll env pre ~start:node g =
        if find_depth node <= 0 then
          env
        else
          begin
            decr_depth node;
            let env = !wp_rec_call env pre ~start:node g in
            unroll env pre ~start:node g
          end
      in
      unroll
  }

let mk_env
    ?subs:(subs = Seq.empty)
    ?exp_conds:(exp_conds = [])
    ~specs:(specs : (Sub.t -> fun_spec option) list)
    ~default_spec:(default_spec : fun_spec)
    ~jmp_spec:(jmp_spec : jmp_spec)
    ~int_spec:(int_spec : int_spec)
    ~num_loop_unroll:(num_loop_unroll : int)
    (ctx : Z3.context)
    (var_gen : var_gen)
  : t =
  {
    ctx = ctx;
    var_gen = var_gen;
    subs = subs;
    var_map = EnvMap.empty;
    precond_map = TidMap.empty;
    fun_name_tid = init_fun_name subs;
    call_map = init_call_map var_gen subs;
    sub_handler = init_sub_handler subs ~specs:specs ~default_spec:default_spec;
    jmp_handler = jmp_spec;
    int_handler = int_spec;
    loop_handler = init_loop_unfold num_loop_unroll;
    exp_conds = exp_conds
  }

let env_to_string (env : t) : string =
  let pair_printer ts1 ts2 f (x,y) = Format.fprintf f "%s -> \n%s\n" (ts1 x) (ts2 y) in
  let map_seq_printer ts1 ts2 f seq = Seq.pp (pair_printer ts1 ts2) f seq in
  let var_list = env.var_map |> EnvMap.to_sequence in
  let sub_list = env.sub_handler |> TidMap.to_sequence in
  let call_list = env.call_map |> TidMap.to_sequence in
  let precond_list = env.precond_map |> TidMap.to_sequence in
  Format.asprintf "Vars: %a\nSubs: %a\nCalls: %a\nPreconds: %a%!"
    (map_seq_printer Var.to_string Expr.to_string) var_list
    (map_seq_printer Tid.to_string (fun s -> s.spec_name)) sub_list
    (map_seq_printer Tid.to_string ident) call_list
    (map_seq_printer Tid.to_string Expr.to_string) precond_list

let add_var (env : t) (v : Var.t) (x : z3_expr) : t =
  { env with var_map = EnvMap.set env.var_map ~key:v ~data:x }

let add_precond (env : t) (tid : Tid.t) (p : z3_expr) : t =
  { env with precond_map = TidMap.set env.precond_map ~key:tid ~data:p }

let mk_exp_conds (env : t) (e : exp) : z3_expr list * z3_expr list =
  let { exp_conds; _ } = env in
  let conds = List.map exp_conds ~f:(fun gen -> gen env e) in
  let conds = List.filter_opt conds in
  List.partition_map conds
    ~f:(function | Assume cond -> `Fst cond | Verify cond -> `Snd cond)

let get_context (env : t) : Z3.context =
  env.ctx

let get_var_gen (env : t) : var_gen =
  env.var_gen

let get_subs (env : t) : Sub.t Seq.t =
  env.subs

let get_var_map (env : t) : z3_expr EnvMap.t =
  env.var_map

let get_var (env : t) (var : Var.t) : z3_expr option =
  EnvMap.find env.var_map var

let get_precondition (env : t) (tid : Tid.t) : z3_expr option =
  if not (TidMap.mem env.precond_map tid) then
    warning "Precondition for block %s not found!%!" (Tid.to_string tid);
  TidMap.find env.precond_map tid

let get_fun_name_tid (env : t) (f : string) : Tid.t option =
  StringMap.find env.fun_name_tid f

let get_called (env : t) (tid : Tid.t) : string option =
  TidMap.find env.call_map tid

let get_sub_handler (env : t) (tid : Tid.t) : fun_spec_type option =
  match TidMap.find env.sub_handler tid with
  | Some compute_func -> Some compute_func.spec
  | None -> None

let get_jmp_handler (env : t) : jmp_spec =
  env.jmp_handler

let get_int_handler (env : t) : int_spec =
  env.int_handler

let get_loop_handler (env : t) :
  t -> z3_expr -> start:Graphs.Ir.Edge.node -> Graphs.Ir.t -> t =
  env.loop_handler.handle

let fold_fun_tids (env : t) ~init:(init : z3_expr)
    ~f:(f : key:string -> data:Tid.t -> z3_expr -> z3_expr) : z3_expr =
  StringMap.fold env.fun_name_tid ~init:init ~f:f