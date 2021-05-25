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
open Bap.Std
open Bap_core_theory

include Self()

module Bool = Z3.Boolean
module BV = Z3.BitVector
module Expr = Z3.Expr
module Constr = Constraint

(* The environment for computing the semantics of an instruction *)
module EnvMap = Var.Map
module TidMap = Tid.Map
module StringMap = String.Map

exception Not_implemented of string

module ExprSet = Set.Make(
  struct
    type t = Constr.z3_expr
    let compare = Expr.compare
    let sexp_of_t _ = raise (Not_implemented "sexp_of_t for z3_expr not implemented")
    let t_of_sexp _ = raise (Not_implemented "t_of_sexp for z3_expr not implemented")
  end)

module Unroll_depth = Blk.Map

type unroll_depth = int Unroll_depth.t

type loop_invariants = string Tid.Map.t

type var_gen = int ref

type mem_range = {
  (* The base address is the highest address on the stack and the lowest
     address on the data section. *)
  base_addr : int;
  (* Memory size in bytes. *)
  size : int
}

type t = {
  freshen : bool;
  ctx : Z3.context;
  var_gen : var_gen;
  subs : Sub.t Seq.t;
  var_map : Constr.z3_expr EnvMap.t;
  precond_map : Constr.t TidMap.t;
  fun_name_tid : Tid.t StringMap.t;
  call_map : string TidMap.t;
  sub_handler : fun_spec TidMap.t;
  indirect_handler : indirect_spec;
  jmp_handler : jmp_spec;
  int_handler : int_spec;
  loop_handler : loop_handler;
  unroll_depth : unroll_depth;
  exp_conds : exp_cond list;
  target : Theory.target;
  use_fun_input_regs : bool;
  stack : mem_range;
  data_section : mem_range;
  init_vars : Constr.z3_expr EnvMap.t;
  call_preds : ExprSet.t;
  func_name_map : string StringMap.t;
  smtlib_compat : bool
}

and fun_spec_type =
  | Summary of (t -> Constr.t -> Tid.t -> Constr.t * t)
  | Inline

and fun_spec = {
  spec_name : string;
  spec : fun_spec_type
}

and indirect_spec = t -> Constr.t -> Exp.t -> bool -> Constr.t * t

and jmp_spec = t -> Constr.t -> Tid.t -> Jmp.t -> (Constr.t * t) option

and int_spec = t -> Constr.t -> int -> Constr.t * t

(* Updates the environment with the preconditions computed by
   the loop handling procedure for the appropriate blocks *)
and loop_handler = t -> Constr.t -> start:Graphs.Ir.Node.t -> Graphs.Ir.t -> t

and cond = BeforeExec of Constr.goal | AfterExec of Constr.goal

and cond_type = Verify of cond | Assume of cond

and exp_cond = t -> Bap.Std.Exp.t -> cond_type option

let mk_ctx () : Z3.context = Z3.mk_context []

let mk_var_gen () : int ref = ref 0

let mk_z3_expr (ctx : Z3.context) ~name:(name : string) ~typ:(typ : Type.t) : Constr.z3_expr =
  match typ with
  | Type.Imm size -> Z3.BitVector.mk_const_s ctx name size
  | Type.Mem (i_size, w_size) ->
    debug "Creating memory Mem<%d,%d>%!" (Size.in_bits i_size) (Size.in_bits w_size);
    let i_sort = Z3.BitVector.mk_sort ctx (Size.in_bits i_size) in
    let w_sort = Z3.BitVector.mk_sort ctx (Size.in_bits w_size) in
    Z3.Z3Array.mk_const_s ctx name i_sort w_sort
  | Type.Unk ->
    error "Unk type: Unable to make z3_expr %s.%!" name;
    failwith "mk_z3_expr: type is not representable by Type.t"

let add_precond (env : t) (tid : Tid.t) (p : Constr.t) : t =
  { env with precond_map = TidMap.set env.precond_map ~key:tid ~data:p }

let get_precondition (env : t) (tid : Tid.t) : Constr.t option =
  if not (TidMap.mem env.precond_map tid) then
    warning "Precondition for block %s not found!%!" (Tid.to_string tid);
  TidMap.find env.precond_map tid

let get_context (env : t) : Z3.context =
  env.ctx

let get_mapped_name (name_mod : string) (map : string String.Map.t) : string =
  (* If the name is not in the map, we assume both binaries have the same
     name. *)
  match String.Map.find map name_mod with
  | Some name -> name
  | None -> name_mod

let init_fun_name (subs : Sub.t Seq.t) (name_map : string String.Map.t)
  : Tid.t StringMap.t =
  Seq.fold subs ~init:StringMap.empty
    ~f:(fun map sub ->
        let name = get_mapped_name (Sub.name sub) name_map in
        StringMap.set map ~key:name ~data:(Term.tid sub))

let get_fresh ?name:(n = "fresh_") (var_seed : var_gen) : string =
  incr var_seed;
  n ^ (string_of_int !var_seed)

let new_z3_expr ?name:(name = "fresh_") (env: t) (typ : Type.t) : Constr.z3_expr =
  let ctx = env.ctx in
  let var_seed = env.var_gen in
  mk_z3_expr ctx ~name:(get_fresh ~name:name var_seed) ~typ:typ

let init_call_map (var_gen : var_gen) (subs : Sub.t Seq.t)
    (name_map : string StringMap.t) : string TidMap.t =
  Seq.fold subs ~init:TidMap.empty
    ~f:(fun map sub ->
        let name = get_mapped_name (Sub.name sub) name_map in
        let is_called = get_fresh ~name:("called_" ^ name) var_gen in
        TidMap.set map ~key:(Term.tid sub) ~data:is_called)

let init_sub_handler (subs : Sub.t Seq.t) (target : Theory.target)
    ~specs:(specs : (Sub.t -> Theory.target -> fun_spec option) list)
    ~default_spec:(default_spec : Sub.t -> Theory.target -> fun_spec) : fun_spec TidMap.t =
  Seq.fold subs ~init:TidMap.empty
    ~f:(fun map sub ->
        let spec = List.find_map specs ~f:(fun creator -> creator sub target)
                   |> Option.value ~default:(default_spec sub target) in
        debug "%s: %s%!" (Sub.name sub) spec.spec_name;
        TidMap.set map ~key:(Term.tid sub) ~data:spec)

let init_loop_handler
    ~(default : loop_handler)
    (handlers : (Tid.t -> loop_handler option) list)
  : loop_handler =
  fun env post ~start:node g ->
  let tid = node |> Graphs.Ir.Node.label |> Term.tid in
  let handler = List.find_map handlers ~f:(fun handler -> handler tid)
                |> Option.value ~default in
  handler env post ~start:node g

(* Creates a new environment with
   - a sequence of subroutines in the program used to initialize function specs
   - a list of {!fun_spec}s that each summarize the precondition for its mapped function
   - the default fun_spec in the case a function does not satisfy the requirements
     of the other fun_specs
   - a {!jmp_spec} for handling branches
   - an {!int_spec} for handling interrupts
   - a list of {!exp_cond}s to satisfy
   - a loop handler that can unroll a loop or check a loop invariant
   - the target architecture of the binary
   - the option to freshen variable names
   - the option to use all input registers when generating function symbols at a call site
   - the range of addresses of the stack
   - the range of addresses of the data section
   - a Z3 context
   - and a variable generator. *)
let mk_env
    ~(subs : Sub.t Seq.t)
    ~(specs : (Sub.t -> Theory.target -> fun_spec option) list)
    ~(default_spec : Sub.t -> Theory.target -> fun_spec)
    ~(indirect_spec : indirect_spec)
    ~(jmp_spec : jmp_spec)
    ~(int_spec : int_spec)
    ~(exp_conds : exp_cond list)
    ~(loop_handlers : (Tid.t -> loop_handler option) list)
    ~(default_loop_handler : loop_handler)
    ~(target : Theory.target)
    ~(freshen_vars : bool)
    ~(use_fun_input_regs : bool)
    ~(stack_range : mem_range)
    ~(data_section_range : mem_range)
    ~(func_name_map : string StringMap.t)
    ~(smtlib_compat : bool)
    (ctx : Z3.context)
    (var_gen : var_gen)
  : t =
  {
    freshen = freshen_vars;
    ctx = ctx;
    var_gen = var_gen;
    subs = subs;
    var_map = EnvMap.empty;
    precond_map = TidMap.empty;
    fun_name_tid = init_fun_name subs func_name_map;
    call_map = init_call_map var_gen subs func_name_map;
    sub_handler = init_sub_handler subs target ~specs:specs ~default_spec:default_spec;
    indirect_handler = indirect_spec;
    jmp_handler = jmp_spec;
    int_handler = int_spec;
    loop_handler = init_loop_handler ~default:default_loop_handler loop_handlers;
    unroll_depth = Unroll_depth.empty;
    exp_conds = exp_conds;
    target = target;
    use_fun_input_regs = use_fun_input_regs;
    stack = stack_range;
    data_section = data_section_range;
    init_vars = EnvMap.empty;
    call_preds = ExprSet.empty;
    func_name_map = func_name_map;
    smtlib_compat = smtlib_compat
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
    (map_seq_printer Tid.to_string Constr.to_string) precond_list

let set_freshen (env : t) (freshen : bool) = { env with freshen = freshen }

let add_var (env : t) (v : Var.t) (x : Constr.z3_expr) : t =
  { env with var_map = EnvMap.set env.var_map ~key:v ~data:x }

let add_call_pred (env : t) (c : Constr.z3_expr) : t =
  { env with call_preds = ExprSet.add env.call_preds c }

let clear_call_preds (env : t) : t =
  { env with call_preds = ExprSet.empty }

let remove_var (env : t) (v : Var.t) : t =
  { env with var_map = EnvMap.remove env.var_map v }

let mk_exp_conds (env : t) (e : exp) : cond_type list =
  let { exp_conds; _ } = env in
  List.filter_map exp_conds ~f:(fun gen -> gen env e)

let get_var_gen (env : t) : var_gen =
  env.var_gen

let get_subs (env : t) : Sub.t Seq.t =
  env.subs

let get_var_map (env : t) : Constr.z3_expr EnvMap.t =
  env.var_map

let get_init_var_map (env : t) : Constr.z3_expr EnvMap.t =
  env.init_vars

let find_var (env : t) (var : Var.t) : Constr.z3_expr option =
  EnvMap.find env.var_map var

let get_var (env : t) (var : Var.t) : Constr.z3_expr * t =
  let mv = EnvMap.find env.var_map var in
  match mv with
  | Some v -> v, env
  | None ->
    let typ = Var.typ var in
    let full_name = Var.name var ^ (string_of_int (Var.index var)) in
    if env.freshen then
      let v = new_z3_expr ~name:full_name env typ in
      v, add_var env var v
    else
      let ctx = env.ctx in
      let v = mk_z3_expr ctx ~name:full_name ~typ:typ in
      v, add_var env var v

let get_sub_name (env : t) (tid : Tid.t) : string option =
  Seq.find_map env.subs ~f:(fun s ->
      if Tid.equal tid (Term.tid s) then
        Some (Sub.name s)
      else
        None)

let get_fun_name_tid (env : t) (f : string) : Tid.t option =
  StringMap.find env.fun_name_tid f

let get_called (env : t) (tid : Tid.t) : string option =
  TidMap.find env.call_map tid

let get_sub_handler (env : t) (tid : Tid.t) : fun_spec_type option =
  match TidMap.find env.sub_handler tid with
  | Some compute_func -> Some compute_func.spec
  | None -> None

let get_indirect_handler (env : t) (_exp : Exp.t) : indirect_spec =
  env.indirect_handler

let get_jmp_handler (env : t) : jmp_spec =
  env.jmp_handler

let set_jmp_handler (env : t) (spec : jmp_spec) : t =
  { env with jmp_handler = spec }

let get_int_handler (env : t) : int_spec =
  env.int_handler

let get_loop_handler (env : t) : loop_handler =
  env.loop_handler

let get_call_preds (env : t) : ExprSet.t =
  env.call_preds

let get_target (env : t) : Theory.target =
  env.target

(* The comparator value for Var.t sets. We use this to convert a
   [Theory.Var.Top.Set.t] to a [Var.Set.t] *)
let var_comp : (_, _) Set.comparator = (module Var.Set.Elt)

let get_gprs (env : t) : Bap.Std.Var.Set.t =
  Theory.Target.regs
    ~roles:[Theory.Role.Register.general]
    (get_target env) |>
  Set.map var_comp ~f:Var.reify

let get_sp (env : t) : Var.t =
  let target = get_target env in
  let error =
    Format.asprintf "Stack pointer not found for target: %a"
      Theory.Target.pp target
  in
  let sp = Theory.Target.reg (get_target env)
      Theory.Role.Register.stack_pointer
  in
  Option.value_exn ~message:error sp |> Var.reify

let get_mem (env : t) : Var.t =
  Theory.Target.data (get_target env) |> Var.reify

let fold_fun_tids (env : t) ~init:(init : 'a)
    ~f:(f : key:string -> data:Tid.t -> 'a -> 'a) : 'a =
  StringMap.fold env.fun_name_tid ~init:init ~f:f

let is_x86 (a : Theory.target) : bool =
  Theory.Target.matches a "x86"

let use_input_regs (env : t) : bool =
  env.use_fun_input_regs

(** Determine whether to generate constraints that are smtlib compatible or using
    optimizations that are Z3 specific. Put to [true] if using external smt solver *)
let get_smtlib_compat (env : t) : bool = env.smtlib_compat

(* Returns a function that takes in a memory address as a z3_expr and outputs a
   z3_expr that checks if that address is within the region of stack we are
   defining for the hypothesis. *)
let init_stack_ptr (env : t) : Constr.z3_expr -> Constr.z3_expr =
  let ctx = get_context env in
  let target = get_target env in
  let sort = target |> Theory.Target.data_addr_size |> BV.mk_sort ctx in
  let size = Expr.mk_numeral_int ctx env.stack.size sort in
  let max = Expr.mk_numeral_int ctx env.stack.base_addr sort in
  let min = BV.mk_add ctx (BV.mk_sub ctx max size) (Expr.mk_numeral_int ctx 128 sort) in
  fun addr ->
    assert (BV.is_bv addr);
    Bool.mk_and ctx [BV.mk_ult ctx min addr; BV.mk_ule ctx addr max]

(* Returns a function that takes in a memory address as a z3_expr and outputs a
   z3_expr that checks if that address is within the stack. *)
let in_stack (env : t) : Constr.z3_expr -> Constr.z3_expr =
  let ctx = get_context env in
  let target = get_target env in
  let sort = target |> Theory.Target.data_addr_size |> BV.mk_sort ctx in
  let size = Expr.mk_numeral_int ctx env.stack.size sort in
  let max = Expr.mk_numeral_int ctx env.stack.base_addr sort in
  let min = BV.mk_sub ctx max size in
  fun addr ->
    assert (BV.is_bv addr);
    Bool.mk_and ctx [BV.mk_ult ctx min addr; BV.mk_ule ctx addr max]

let get_stack_end (env : t) : int =
  env.stack.base_addr - env.stack.size

(* Returns a function that takes in a memory address as a z3_expr and outputs a
   z3_expr that checks if that address is within the data section. *)
let in_data_section (env : t) : Constr.z3_expr -> Constr.z3_expr =
  let ctx = get_context env in
  let target = get_target env in
  let sort = target |> Theory.Target.data_addr_size |> BV.mk_sort ctx in
  let size = Expr.mk_numeral_int ctx env.data_section.size sort in
  let min = Expr.mk_numeral_int ctx env.data_section.base_addr sort in
  let max = BV.mk_add ctx min size in
  fun addr ->
    assert (BV.is_bv addr);
    Bool.mk_and ctx [BV.mk_ule ctx min addr; BV.mk_ult ctx addr max]

let update_stack_base (range : mem_range) (base : int) : mem_range =
  { range with base_addr = base }

let update_stack_size (range : mem_range) (size : int) : mem_range =
  { range with size = size }

(* Remove the '|' from a constraint for printing purposes and for support for
   other smt solvers. *)
let clean_name (name : string) : string =
  String.strip ~drop:(fun c -> Char.equal c '|') name

let mk_init_var (env : t) (var : Var.t) : Constr.z3_expr * t =
  let ctx = get_context env in
  let z3_var, _ = get_var env var in
  let sort = Expr.get_sort z3_var in
  let name = Format.sprintf "init_%s" (clean_name (Expr.to_string z3_var)) in
  let init_var = Expr.mk_const_s ctx name sort in
  let env = { env with init_vars = EnvMap.set env.init_vars ~key:var ~data:init_var } in
  init_var, env

let get_init_var (env : t) (var : Var.t) : Constr.z3_expr option =
  EnvMap.find env.init_vars var

let map_sub_name (env : t) (name_mod : string) : string =
  get_mapped_name name_mod env.func_name_map

let get_unroll_depth (env : t) (node : Blk.t) : int option =
  Unroll_depth.find env.unroll_depth node

let set_unroll_depth (env : t) (node : Blk.t) ~(f : int option -> int) : t =
  let updated_depth = Unroll_depth.update env.unroll_depth node ~f in
  { env with unroll_depth = updated_depth }

let freshen ?(name = Format.sprintf "fresh_%s") (constr : Constr.t)
    (env : t) (vars : Var.Set.t) : Constr.t * t =
  let substitutions =
    List.map (Var.Set.to_list vars) ~f:(fun v ->
        let z3_v, env = get_var env v in
        let name = name (clean_name (Expr.to_string z3_v)) in
        let fresh = new_z3_expr ~name env (Var.typ v) in
        (z3_v, fresh))
  in
  let subs_from, subs_to = List.unzip substitutions in
  let env = List.fold subs_to ~init:env ~f:(fun env sub_to ->
      add_call_pred env sub_to) in
  Constr.substitute constr subs_from subs_to, env
