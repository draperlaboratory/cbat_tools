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
open Graphlib.Std

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
  exp_conds : exp_cond list;
  arch : Arch.t;
  use_fun_input_regs : bool;
  stack : mem_range;
  data_section : mem_range;
  init_vars : Constr.z3_expr EnvMap.t;
  consts : ExprSet.t
}

and fun_spec_type =
  | Summary of (t -> Constr.t -> Tid.t -> Constr.t * t)
  | Inline

and fun_spec = {
  spec_name : string;
  spec : fun_spec_type
}

and indirect_spec = t -> Constr.t -> Exp.t -> Constr.t * t

and jmp_spec = t -> Constr.t -> Tid.t -> Jmp.t -> (Constr.t * t) option

and int_spec = t -> Constr.t -> int -> Constr.t * t

and loop_handler = {
  (* Updates the environment with the preconditions computed by
     the loop handling procedure for the appropriate blocks *)
  handle : t -> Constr.t -> start:Graphs.Ir.Node.t -> Graphs.Ir.t -> t
}

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

let init_fun_name (subs : Sub.t Seq.t) : Tid.t StringMap.t =
  Seq.fold subs ~init:StringMap.empty
    ~f:(fun map sub ->
        StringMap.set map ~key:(Sub.name sub) ~data:(Term.tid sub))

let get_fresh ?name:(n = "fresh_") (var_seed : var_gen) : string =
  incr var_seed;
  n ^ (string_of_int !var_seed)

let new_z3_expr ?name:(name = "fresh_") (env: t) (typ : Type.t) : Constr.z3_expr =
  let ctx = env.ctx in
  let var_seed = env.var_gen in
  mk_z3_expr ctx ~name:(get_fresh ~name:name var_seed) ~typ:typ

let init_call_map (var_gen : var_gen) (subs : Sub.t Seq.t) : string TidMap.t =
  Seq.fold subs ~init:TidMap.empty
    ~f:(fun map sub ->
        let is_called = get_fresh ~name:("called_" ^ (Sub.name sub)) var_gen in
        TidMap.set map ~key:(Term.tid sub) ~data:is_called)

let init_sub_handler (subs : Sub.t Seq.t) (arch : Arch.t)
    ~specs:(specs : (Sub.t -> Arch.t -> fun_spec option) list)
    ~default_spec:(default_spec : Sub.t -> Arch.t -> fun_spec) : fun_spec TidMap.t =
  Seq.fold subs ~init:TidMap.empty
    ~f:(fun map sub ->
        let spec = List.find_map specs ~f:(fun creator -> creator sub arch)
                   |> Option.value ~default:(default_spec sub arch) in
        debug "%s: %s%!" (Sub.name sub) spec.spec_name;
        TidMap.set map ~key:(Term.tid sub) ~data:spec)

(* FIXME: this is something of a hack: we use a function ref as a
   place holder for the WP transform for subroutines, which itself is
   needed in the loop handler defined in the environment.

   It will be substituted by the actual visit_sub function at the
   point of definition. This is used to simulate "open recursion".  *)
let wp_rec_call :
  (t -> Constr.t -> start:Graphs.Ir.Node.t -> Graphs.Ir.t -> t) ref =
  ref (fun _ _ ~start:_ _ -> assert false)

let trivial_constr (env : t) : Constr.t =
  get_context env
  |> Z3.Boolean.mk_true
  |> Constr.mk_goal "true"
  |> Constr.mk_constr

(* Looks up the precondition of the exit node of a loop by:
   - obtaining the post dominator tree
   - for each node in the SCC, find its parent in the dominator tree
   - if the parent node is not in the original SCC, it is an exit node *)
let loop_exit_pre (env : t) (node : Graphs.Ir.Node.t) (graph : Graphs.Ir.t)
  : Constr.t option =
  let module Node = Graphs.Ir.Node in
  let scc = Graphlib.strong_components (module Graphs.Ir) graph in
  match Partition.group scc node with
  | None -> None
  | Some g ->
    let leaf = Seq.find (Graphlib.postorder_traverse (module Graphs.Ir) graph)
        ~f:(fun n -> Seq.is_empty (Node.succs n graph))
    in
    match leaf with
    | None -> None
    | Some l ->
      let dom_tree = Graphlib.dominators (module Graphs.Ir) ~rev:true graph l in
      let exit_node = Seq.find_map (Group.enum g) ~f:(fun n ->
          match Tree.parent dom_tree n with
          | None -> None
          | Some p ->
            if Group.mem g p then
              None
            else
              Some (p |> Node.label |> Term.tid)
        ) in
      match exit_node with
      | None -> None
      | Some e ->
        debug "Using precondition from node %s%!" (Tid.to_string e);
        get_precondition env e


module Unfold_depth = Blk.Map

type unfold_depth = int Unfold_depth.t

(* This is the default handler for loops, which unfolds a loop by:
   - Looking at the target node for a backjump
   - If the node has been visited more than [num_unroll] times, use the [loop_exit_pre] precondition
   - Otherwise, decrement the [depth] map which tracks the unfoldings for that node, and
     recursively call [Precondition.visit_graph]. Because this function is defined in another
     (later) module, we use open recursion via the [wp_rec_call] function reference. *)
let rec loop_unfold (num_unroll : int) (depth : unfold_depth) : loop_handler =
  {
    handle =
      let module Node = Graphs.Ir.Node in
      let find_depth node = Unfold_depth.find depth (Node.label node)
                            |> Option.value ~default:num_unroll
      in
      let decr_depth node =
        Unfold_depth.update depth (Node.label node)
          ~f:(function None -> num_unroll - 1 | Some n -> n - 1)
      in
      let unroll env pre ~start:node g =
        if find_depth node <= 0 then
          let tid = node |> Node.label |> Term.tid in
          let pre =
            match List.find_map [loop_exit_pre] ~f:(fun spec -> spec env node g) with
            | Some p -> p
            | None ->
              warning "Trivial precondition is being used for node %s%!" (Tid.to_string tid);
              trivial_constr env
          in
          add_precond env tid pre
        else
          begin
            let updated_depth = decr_depth node in
            let updated_handle = loop_unfold num_unroll updated_depth in
            let updated_env = { env with loop_handler = updated_handle } in
            !wp_rec_call updated_env pre ~start:node g
          end
      in
      unroll
  }


let init_loop_unfold (num_unroll : int) : loop_handler = loop_unfold num_unroll Unfold_depth.empty

(* Creates a new environment with
   - a sequence of subroutines in the program used to initialize function specs
   - a list of {!fun_spec}s that each summarize the precondition for its mapped function
   - the default fun_spec in the case a function does not satisfy the requirements
     of the other fun_specs
   - a {!jmp_spec} for handling branches
   - an {!int_spec} for handling interrupts
   - a list of {!exp_cond}s to satisfy
   - the number of times to unroll a loop
   - the architecture of the binary
   - the option to freshen variable names
   - the option to use all input registers when generating function symbols at a call site
   - the range of addresses of the stack
   - the range of addresses of the data section
   - a Z3 context
   - and a variable generator. *)
let mk_env
    ~subs:(subs : Sub.t Seq.t)
    ~specs:(specs : (Sub.t -> Arch.t -> fun_spec option) list)
    ~default_spec:(default_spec : Sub.t -> Arch.t -> fun_spec)
    ~indirect_spec:(indirect_spec : indirect_spec)
    ~jmp_spec:(jmp_spec : jmp_spec)
    ~int_spec:(int_spec : int_spec)
    ~exp_conds:(exp_conds : exp_cond list)
    ~num_loop_unroll:(num_loop_unroll : int)
    ~arch:(arch : Arch.t)
    ~freshen_vars:(freshen_vars : bool)
    ~use_fun_input_regs:(fun_input_regs : bool)
    ~stack_range:(stack_range : mem_range)
    ~data_section_range:(data_section_range : mem_range)
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
    fun_name_tid = init_fun_name subs;
    call_map = init_call_map var_gen subs;
    sub_handler = init_sub_handler subs arch ~specs:specs ~default_spec:default_spec;
    indirect_handler = indirect_spec;
    jmp_handler = jmp_spec;
    int_handler = int_spec;
    loop_handler = init_loop_unfold num_loop_unroll;
    exp_conds = exp_conds;
    arch = arch;
    use_fun_input_regs = fun_input_regs;
    stack = stack_range;
    data_section = data_section_range;
    init_vars = EnvMap.empty;
    consts = ExprSet.empty
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

let add_const (env : t) (c : Constr.z3_expr) : t =
  { env with consts = ExprSet.add env.consts c }

let clear_consts (env : t) : t =
  { env with consts = ExprSet.empty }

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

let get_int_handler (env : t) : int_spec =
  env.int_handler

let get_loop_handler (env : t) :
  t -> Constr.t -> start:Graphs.Ir.Node.t -> Graphs.Ir.t -> t =
  env.loop_handler.handle

let get_consts (env : t) : ExprSet.t =
  env.consts

let get_arch (env : t) : Arch.t =
  env.arch

let fold_fun_tids (env : t) ~init:(init : 'a)
    ~f:(f : key:string -> data:Tid.t -> 'a -> 'a) : 'a =
  StringMap.fold env.fun_name_tid ~init:init ~f:f

let is_x86 (a : Arch.t) : bool =
  match a with
  | #Arch.x86 -> true
  | _ -> false

let use_input_regs (env : t) : bool =
  env.use_fun_input_regs

(* Returns a function that takes in a memory address as a z3_expr and outputs a
   z3_expr that checks if that address is within the region of stack we are
   defining for the hypothesis. *)
let init_stack_ptr (env : t) : Constr.z3_expr -> Constr.z3_expr =
  let ctx = get_context env in
  let arch = get_arch env in
  let sort = arch |> Arch.addr_size |> Size.in_bits |> BV.mk_sort ctx in
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
  let arch = get_arch env in
  let sort = arch |> Arch.addr_size |> Size.in_bits |> BV.mk_sort ctx in
  let size = Expr.mk_numeral_int ctx env.stack.size sort in
  let max = Expr.mk_numeral_int ctx env.stack.base_addr sort in
  let min = BV.mk_sub ctx max size in
  fun addr ->
    assert (BV.is_bv addr);
    Bool.mk_and ctx [BV.mk_ult ctx min addr; BV.mk_ule ctx addr max]

(* Returns a function that takes in a memory address as a z3_expr and outputs a
   z3_expr that checks if that address is within the data section. *)
let in_data_section (env : t) : Constr.z3_expr -> Constr.z3_expr =
  let ctx = get_context env in
  let arch = get_arch env in
  let sort = arch |> Arch.addr_size |> Size.in_bits |> BV.mk_sort ctx in
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

let mk_init_var (env : t) (var : Var.t) : Constr.z3_expr * t =
  let ctx = get_context env in
  let z3_var, _ = get_var env var in
  let sort = Expr.get_sort z3_var in
  let name = Format.sprintf "init_%s" (Expr.to_string z3_var) in
  let init_var = Expr.mk_const_s ctx name sort in
  let env = { env with init_vars = EnvMap.set env.init_vars ~key:var ~data:init_var } in
  init_var, env

let get_init_var (env : t) (var : Var.t) : Constr.z3_expr option =
  EnvMap.find env.init_vars var
