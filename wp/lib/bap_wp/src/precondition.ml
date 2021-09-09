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
open Bap_core_theory
open Utils.Option_let

include Self()

module Expr = Z3.Expr
module Arith = Z3.Arithmetic
module BV = Z3.BitVector
module Bool = Z3.Boolean
module Z3Array = Z3.Z3Array
module FuncDecl = Z3.FuncDecl
module Solver = Z3.Solver
module Env = Environment
module Constr = Constraint

exception Not_implemented of string

type hooks = {
  assume_before : Constr.t list;
  assume_after : Constr.t list;
  verify_before : Constr.t list;
  verify_after : Constr.t list;
}

let z3_expr_zero (ctx : Z3.context) (size : int) : Constr.z3_expr = BV.mk_numeral ctx "0" size
let z3_expr_one (ctx : Z3.context) (size : int) : Constr.z3_expr = BV.mk_numeral ctx "1" size

let binop ?(smtlib_compat = false) (ctx : Z3.context) (b : binop) :
  Constr.z3_expr -> Constr.z3_expr -> Constr.z3_expr =
  let open Bap.Std.Bil.Types in
  let zero = z3_expr_zero ctx 1 in
  let one = z3_expr_one ctx 1 in
  match b with
  | PLUS -> BV.mk_add ctx
  | MINUS -> BV.mk_sub ctx
  | TIMES -> BV.mk_mul ctx
  | DIVIDE -> BV.mk_udiv ctx
  | SDIVIDE -> BV.mk_sdiv ctx
  | MOD -> BV.mk_urem ctx
  | SMOD -> BV.mk_smod ctx
  | LSHIFT -> BV.mk_shl ctx
  | RSHIFT -> BV.mk_lshr ctx
  | ARSHIFT -> BV.mk_ashr ctx
  | AND -> BV.mk_and ctx
  | OR -> BV.mk_or ctx
  | XOR -> BV.mk_xor ctx
  | EQ -> fun x y -> if smtlib_compat then (Bool.mk_ite ctx (Bool.mk_eq ctx x y) one zero)
    else  (BV.mk_not ctx @@ BV.mk_redor ctx @@ BV.mk_xor ctx x y)
  | NEQ -> fun x y -> if smtlib_compat
    then  Bool.mk_ite ctx (Bool.mk_eq ctx x y) zero one
    else  BV.mk_redor ctx @@ BV.mk_xor ctx x y
  | LT -> fun x y -> Bool.mk_ite ctx (BV.mk_ult ctx x y) one zero
  | LE -> fun x y -> Bool.mk_ite ctx (BV.mk_ule ctx x y) one zero
  | SLT -> fun x y -> Bool.mk_ite ctx (BV.mk_slt ctx x y) one zero
  | SLE -> fun x y -> Bool.mk_ite ctx (BV.mk_sle ctx x y) one zero

let unop (ctx : Z3.context) (u : unop) : Constr.z3_expr -> Constr.z3_expr =
  let open Bap.Std.Bil.Types in
  match u with
  | NEG -> BV.mk_neg ctx
  | NOT -> BV.mk_not ctx

let cast (ctx : Z3.context) (cst : cast) (i : int) (x : Constr.z3_expr) : Constr.z3_expr =
  assert (i > 0);
  let size = x |> Expr.get_sort |> BV.get_size in
  let open Bap.Std.Bil.Types in
  match cst with
  | UNSIGNED -> BV.mk_zero_ext ctx (i - size) x
  | SIGNED -> BV.mk_sign_ext ctx (i - size) x
  | HIGH -> BV.mk_extract ctx (size - 1) (size - i) x
  | LOW -> BV.mk_extract ctx (i - 1) 0 x

(* Placeholder for inlining function calls, which will be substituted with [visit_sub]
   at its point of definition. *)
let inline_func :
  (Constr.t -> Env.t -> Tid.t -> Constr.t * Env.t) ref =
  ref (fun _ _ _ -> assert false)

let load_z3_mem (ctx : Z3.context) ~word_size:word_size ~mem:(mem : Constr.z3_expr)
    ~addr:(addr : Constr.z3_expr) (endian : Bap.Std.endian) : Constr.z3_expr =
  assert (Z3Array.is_array mem && mem |> Expr.get_sort
                                  |> Z3Array.get_range
                                  |> Z3.Sort.get_sort_kind
                                  |> (function
                                      | Z3enums.BV_SORT -> true
                                      |_ -> false));
  let m_size = mem |> Expr.get_sort |> Z3Array.get_range |> BV.get_size in
  let addr_size = addr |> Expr.get_sort |> BV.get_size in
  let nums_to_read = word_size / m_size in
  debug "Creating load on Mem<%d,%d>, with target Imm<%d>%!" addr_size m_size word_size;
  assert (nums_to_read > 0);
  let rec read_list n addr reads =
    if n = 0 then reads
    else
      (* TODO: handle overflow *)
      let addr' = BV.mk_add ctx addr (z3_expr_one ctx addr_size) in
      read_list (n-1) addr' (Z3Array.mk_select ctx mem addr :: reads)
  in
  let read = read_list nums_to_read addr [] in
  let read_sorted =
    match endian with
    | BigEndian -> List.rev read
    | LittleEndian -> read
  in
  List.reduce_exn read_sorted ~f:(BV.mk_concat ctx)

let store_z3_mem (ctx : Z3.context) ~word_size:word_size
    ~mem:(mem : Constr.z3_expr) ~addr:(addr : Constr.z3_expr) ~content:(e : Constr.z3_expr)
    (endian : Bap.Std.endian) : Constr.z3_expr =
  assert (Z3Array.is_array mem && mem |> Expr.get_sort
                                  |> Z3Array.get_range
                                  |> Z3.Sort.get_sort_kind
                                  |> (function
                                      | Z3enums.BV_SORT -> true
                                      | _ -> false));
  let m_size = mem |> Expr.get_sort |> Z3Array.get_range |> BV.get_size in
  let addr_size = addr |> Expr.get_sort |> BV.get_size in
  let nums_to_write = word_size / m_size in
  let first_loc, next_loc =
    match endian with
    | BigEndian -> word_size - m_size, fun l -> l - m_size
    | LittleEndian -> 0, fun l -> l + m_size
  in
  assert (nums_to_write > 0);
  let rec store n loc addr mem =
    if n = 0 then mem
    else
      begin
        (* TODO: handle overflow *)
        debug "Storing bits %d to %d at position %s%!"
          loc (loc + m_size - 1) (Expr.to_string addr);
        let e_chunk_n = BV.mk_extract ctx (loc + m_size - 1) loc e in
        let mem' = Z3Array.mk_store ctx mem addr e_chunk_n in
        let addr' = BV.mk_add ctx addr (z3_expr_one ctx addr_size) in
        store (n-1) (next_loc loc) addr' mem'
      end
  in
  debug "Creating store on Mem<%d,%d>, with target Imm<%d>%!" addr_size m_size word_size;
  store nums_to_write first_loc addr mem

let bv_to_bool (bv : Constr.z3_expr) (ctx : Z3.context) (width : int) : Constr.z3_expr =
  let zero = z3_expr_zero ctx width in
  Bool.mk_not ctx (Bool.mk_eq ctx bv zero)

(* Sorts a list of [cond_type]s into a record which separates each hook into assumptions,
   VCs, and whether these conditions should be added to the postcondition before or
   after execution. *)
let mk_hooks (conds : Env.cond_type list) : hooks =
  let hooks =
    { assume_before = []; assume_after = []; verify_before = []; verify_after = [] } in
  List.fold conds ~init:hooks ~f:(fun hooks cond ->
      match cond with
      | Assume (BeforeExec c) ->
        { hooks with assume_before = Constr.mk_constr c :: hooks.assume_before }
      | Assume (AfterExec c) ->
        { hooks with assume_after = Constr.mk_constr c :: hooks.assume_after }
      | Verify (BeforeExec c) ->
        { hooks with verify_before = Constr.mk_constr c :: hooks.verify_before }
      | Verify (AfterExec c) ->
        { hooks with verify_after = Constr.mk_constr c :: hooks.verify_after }
    )

let hooks_to_string (h : hooks) : string =
  Format.sprintf "VCs before exec:%s\nVCs after exec:%s\n \
                  Assumptions before exec:%s\nAssumptions after exec:%s\n%!"
    (List.to_string ~f:Constr.to_string h.verify_before)
    (List.to_string ~f:Constr.to_string h.verify_after)
    (List.to_string ~f:Constr.to_string h.assume_before)
    (List.to_string ~f:Constr.to_string h.assume_after)

let word_to_z3 (ctx : Z3.context) (w : Word.t) : Constr.z3_expr =
  let fmt = Format.str_formatter in
  Word.pp_dec fmt w;
  let s = Format.flush_str_formatter () in
  BV.mk_numeral ctx s (Word.bitwidth w)

let exp_to_z3 (exp : Exp.t) (env : Env.t) : Constr.z3_expr * hooks * Env.t =
  let ctx = Env.get_context env in
  let open Bap.Std.Bil.Types in
  let rec exp_to_z3_body exp env : Constr.z3_expr * Env.t =
    match exp with
    | Load (mem, addr, endian, size) ->
      debug "Visiting load: Mem:%s  Addr:%s  Size:%s%!"
        (Exp.to_string mem) (Exp.to_string addr) (Size.to_string size);
      let mem_val, env = exp_to_z3_body mem env in
      let addr_val, env = exp_to_z3_body addr env in
      load_z3_mem ctx ~word_size:(Size.in_bits size) ~mem:mem_val ~addr:addr_val endian, env
    | Store (mem, addr, exp, endian, size) ->
      debug "Visiting store: Mem:%s  Addr:%s  Exp:%s  Size:%s%!"
        (Exp.to_string mem) (Exp.to_string addr) (Exp.to_string exp) (Size.to_string size);
      let mem_val, env = exp_to_z3_body mem env in
      let addr_val, env = exp_to_z3_body addr env in
      let exp_val, env = exp_to_z3_body exp env in
      store_z3_mem ctx ~word_size:(Size.in_bits size)
        ~mem:mem_val ~addr:addr_val ~content:exp_val endian, env
    | BinOp (bop, x, y) ->
      debug "Visiting binop: %s %s %s%!"
        (Exp.to_string x) (Bil.string_of_binop bop) (Exp.to_string y);
      let get_size v = v |> Expr.get_sort |> BV.get_size in
      let x_val, env = exp_to_z3_body x env in
      let y_val, env = exp_to_z3_body y env in
      (* In x86 decoding, it is possible to scale the address with a 2-bitwidth shift
         of 0, 1, 2, or 3. However, Z3 requires requires the operands of a bit shift
         to be of the same bitwidth. Here, we pad the operand with the smaller
         bitwidth to match the bitwidth of the other operand. *)
      let x_val, y_val =
        match bop with
        | LSHIFT | RSHIFT | ARSHIFT ->
          let x_size = get_size x_val in
          let y_size = get_size y_val in
          if x_size > y_size then
            x_val, BV.mk_zero_ext ctx (x_size - y_size) y_val
          else if y_size > x_size then
            BV.mk_zero_ext ctx (y_size - x_size) x_val, y_val
          else
            x_val, y_val
        | _ -> x_val, y_val
      in
      assert (get_size x_val = get_size y_val);
      let smtlib_compat = Env.get_smtlib_compat env in
      binop ~smtlib_compat ctx bop x_val y_val, env
    | UnOp (u, x) ->
      debug "Visiting unop: %s %s%!" (Bil.string_of_unop u) (Exp.to_string x);
      let x_val, env = exp_to_z3_body x env in
      unop ctx u x_val, env
    | Var v ->
      debug "Visiting var: %s%!" (Var.to_string v);
      Env.get_var env v
    | Bil.Types.Int w ->
      debug "Visiting int: %s%!" (Word.to_string w);
      word_to_z3 ctx w, env
    | Cast (cst, i, x) ->
      debug "Visiting cast: %s from %d to %s%!"
        (Bil.string_of_cast cst) i (Exp.to_string x);
      let x_val, env = exp_to_z3_body x env in
      cast ctx cst i x_val, env
    | Let (v, exp, body) ->
      debug "Visiting let %s = %s in %s%!"
        (Var.to_string v) (Exp.to_string exp) (Exp.to_string body);
      let exp_val, env = exp_to_z3_body exp env in
      let old_val = Env.find_var env v in
      let env' = Env.add_var env v exp_val in
      let z3_expr, env = exp_to_z3_body body env' in
      let env = Env.remove_var env v in
      let env = match old_val with
        | None -> env
        | Some exp_val -> Env.add_var env v exp_val in
      (z3_expr, env)
    | Unknown (str, typ) ->
      debug "Visiting unknown: %s  Type:%s%!" str (Type.to_string typ);
      Env.new_z3_expr env ~name:("unknown_" ^ str) typ, env
    | Ite (cond, yes, no) ->
      debug "Visiting ite: if %s\nthen %s\nelse %s%!"
        (Exp.to_string cond) (Exp.to_string yes) (Exp.to_string no);
      let cond_val, env = exp_to_z3_body cond env in
      let cond_size = BV.get_size (Expr.get_sort cond_val) in
      let yes_val, env = exp_to_z3_body yes env in
      let no_val, env = exp_to_z3_body no env in
      Bool.mk_ite ctx (bv_to_bool cond_val ctx cond_size) yes_val no_val, env
    | Extract (high, low, exp) ->
      debug "Visiting extract: High:%d Low:%d Exp:%s%!" high low (Exp.to_string exp);
      let exp_val, env = exp_to_z3_body exp env in
      BV.mk_extract ctx high low exp_val, env
    | Concat (w1, w2) ->
      debug "Visiting concat: %s ^ %s%!" (Exp.to_string w1) (Exp.to_string w2);
      let w1_val, env = exp_to_z3_body w1 env in
      let w2_val, env = exp_to_z3_body w2 env in
      BV.mk_concat ctx w1_val w2_val, env
  in
  let exp_conds = Env.mk_exp_conds env exp in
  let hooks = mk_hooks exp_conds in
  let z3_exp, new_env = exp_to_z3_body exp env in
  z3_exp, hooks, new_env

let typ_size (t : Type.t) : int =
  match t with
  | Bil.Types.Imm n -> n
  | Bil.Types.Mem (_, s) -> Size.in_bits s
  | Bil.Types.Unk ->
    error "Unk type: Unable to obtain type size.%!";
    failwith "typ_size: elt's type is not representable by Type.t"

let set_fun_called (post : Constr.t) (env : Env.t) (tid : Tid.t) : Constr.t =
  let ctx = Env.get_context env in
  let fun_name =
    Env.get_called env tid
    |> Option.value_exn ?here:None ?error:None ?message:None
    |> Bool.mk_const_s ctx
  in
  Constr.substitute_one post fun_name (Bool.mk_true ctx)

(* FIXME: handle other architectures *)
let increment_stack_ptr (post : Constr.t) (env : Env.t) : Constr.t * Env.t =
  let target = Env.get_target env in
  if Env.is_x86 target then
    begin
      let sp, env = Env.get_sp env |> Env.get_var env in
      let width = target |> Theory.Target.bits in
      let addr_size = target |> Theory.Target.code_addr_size in
      let addr_size = addr_size / Theory.Target.byte target in
      let ctx = Env.get_context env in
      let offset = BV.mk_numeral ctx (Int.to_string addr_size) width in
      let z3_off = BV.mk_add ctx sp offset in
      Constr.substitute_one post sp z3_off, env
    end
  else
    post, env

let lookup_precond (tid: Bap.Std.Tid.t) (env: Env.t) (post: Constr.t) =
  match Env.get_precondition env tid with
  | Some pre -> pre
  | None ->
    info "Precondition for return %s not found!" (Tid.to_string tid);
    post

let lookup_sub_handler (tid: Bap.Std.Tid.t) (env: Env.t) (post: Constr.t) =
  match Env.get_sub_handler env tid with
  | Some (Summary compute_func) -> compute_func env post tid
  | Some Inline -> !inline_func post env tid
  | None -> post, env

let visit_call (call: Bap.Std.Call.t) (post : Constr.t) (env : Env.t) : Constr.t * Env.t =
  let target = Call.target call in
  let return = Call.return call in
  match target, return with
  | Direct t_tid, Some (Indirect _) ->
    warning "making direct call to %s with indirect return!\n%!"
      (Tid.to_string t_tid);
    post, env
  | Indirect _, Some (Indirect _) ->
    warning "making indirect call with indirect return!\n%!";
    post, env
  | Indirect t_exp, None ->
    warning "Making an indirect call with expression %s with no return;
    applying the default spec (do nothing)!\n%!" (Exp.to_string t_exp);
    Env.get_indirect_handler env t_exp env post t_exp false
  | Direct t_tid, None ->
    debug "Call label %s with no return%!" (Label.to_string target);
    lookup_sub_handler t_tid env post
  | Direct t_tid, Some (Direct r_tid) ->
    let ret_pre = lookup_precond r_tid env post in
    lookup_sub_handler t_tid env ret_pre
  | Indirect t_exp, Some (Direct r_tid) ->
    warning "Making an indirect call with expression %s with return to tid %s;
    incrementing the stack pointer!\n%!"
      (Exp.to_string t_exp) (Tid.to_string r_tid);
    let ret_pre = lookup_precond r_tid env post in
    Env.get_indirect_handler env t_exp env ret_pre t_exp true


let var_of_arg_t (arg : Arg.t) : Var.t =
  let vars = arg |> Arg.rhs |> Exp.free_vars in
  assert (Var.Set.length vars = 1);
  Var.Set.choose_exn vars

(* Creates a Z3 function of the form func_ret_out_var(in_vars, ...) which represents
   an output variable to a function call. It substitutes the original z3_expr
   representing the output variable. *)
let subst_fun_outputs ?tid_name:(tid_name = "") ~inputs:(inputs : Var.t list)
    ~outputs:(outputs : Var.t list) (env : Env.t) (sub : Sub.t) (post : Constr.t)
  : Constr.t * Env.t =
  debug "Chaosing outputs for %s%!" (Sub.name sub);
  let ctx = Env.get_context env in
  let sub_name = Env.map_sub_name env (Sub.name sub) in
  let inputs = List.map inputs
      ~f:(fun i ->
          let input, _ = Env.get_var env i in
          input)
  in
  let input_sorts = List.map inputs ~f:Expr.get_sort in
  let outputs = List.map outputs
      ~f:(fun o ->
          let tid_name = if (String.equal tid_name "") then "" else ("_" ^ tid_name) in
          let name = Format.sprintf "%s%s_ret_%s" sub_name (tid_name) (Var.to_string o) in
          let z3_v, _ = Env.get_var env o in
          let func_decl = FuncDecl.mk_func_decl_s ctx name input_sorts (Expr.get_sort z3_v) in
          let application = FuncDecl.apply func_decl inputs in
          debug "\t%s%!" (Expr.to_string application);
          (z3_v, application))
  in
  let subs_from, subs_to = List.unzip outputs in
  let env = List.fold subs_to ~init:env ~f:(fun env sub_to ->
      Env.add_call_pred env sub_to) in
  Constr.substitute post subs_from subs_to, env

let is_amd64 tgt = Theory.Target.matches tgt "amd64"
let is_i386 tgt = Theory.Target.matches tgt "i386"
let is_arm tgt = Theory.Target.matches tgt "arm"

(* FIXME: use built-in BAP roles? *)
let input_regs (target : Theory.target) : Var.t list =
  if is_amd64 target then
    begin
      let open X86_cpu.AMD64 in
      (* r.(0) and r.(1) refer to registers R8 and R9 respectively.
         Arguments are placed on the stack when they have a higher count than the
         number of registers. We currently do not handle mem as an input because it
         causes Z3 to slow down during evaluation. *)
      info "[mem] is not included as an input to the function call.%!";
      [rdi; rsi; rdx; rcx; r.(0); r.(1)]
    end
  else if is_i386 target then
    begin
      warning "In 32-bit x86, arguments are passed through the stack.%!";
      []
    end
  else if is_arm target then
    begin
      let open ARM.CPU in
      [r0; r1; r2; r3; r12]
    end
  else
    begin
      warning "caller_saved_regs: input registers have not \
               been implemented for %s." (Theory.Target.to_string target);
      []
    end

let caller_saved_regs (target : Theory.target) : Var.t list =
  if is_amd64 target then
    begin
      let open X86_cpu.AMD64 in
      (* Obtains registers r8 - r11 from X86_cpu.AMD64.r. *)
      let r = Array.to_list (Array.sub r ~pos:0 ~len:4) in
      [rax; rcx; rdx; rsi; rdi] @ r
    end
  else if is_i386 target then
    begin
      let open X86_cpu.IA32 in
      [rax; rcx; rdx]
    end
  else if is_arm target then
    begin
      let open ARM.CPU in
      [r0; r1; r2; r3; r12]
    end
  else
    begin
      warning "caller_saved_regs: Caller-saved registers have not \
               been implemented for %s." (Theory.Target.to_string target);
      []
    end

let callee_saved_regs (target : Theory.target) : Var.t list =
  if is_amd64 target then
    begin
      let open X86_cpu.AMD64 in
      (* Obtains registers r12 - r15 from X86_cpu.AMD64.r. *)
      let r = Array.to_list (Array.sub r ~pos:4 ~len:4) in
      [rbx; rsp; rbp] @ r
    end
  else if is_i386 target then
    begin
      let open X86_cpu.IA32 in
      [rbx; rdi; rsi; rsp; rbp]
    end
  else if is_arm target then
    begin
      let open ARM.CPU in
      [r4; r5; r6; r7; r8; r9; r10; r11]
    end
  else
    begin
      warning "callee_saved_regs: Callee-saved registers have not \
               been implemented for %s." (Theory.Target.to_string target);
      []
    end

let rec vars_from_sub (env : Env.t) (t : Sub.t) : Var.Set.t =
  let vars =
    if Env.use_input_regs env then
      env |> Env.get_target |> input_regs |> Var.Set.of_list
    else
      Var.Set.empty
  in
  let visitor =
    (object inherit [Var.Set.t] Term.visitor
      method! visit_arg arg vars =
        Var.Set.add vars (var_of_arg_t arg)
      method! visit_def def vars =
        let vars = Var.Set.add vars (Def.lhs def) in
        let vars = Var.Set.union vars (Def.free_vars def) in
        vars
      method! visit_jmp jmp vars =
        (* If the jump is a call to a target that is to be inlined, visit and
           collect the variables in the target. *)
        let vars = match Jmp.kind jmp with
          | Call call ->
            begin
              match Call.target call with
              | Direct tid ->
                begin
                  match Env.get_sub_handler env tid with
                  | Some Inline ->
                    let subs = Env.get_subs env in
                    let target = Seq.find_exn subs ~f:(fun s -> Tid.equal (Term.tid s) tid) in
                    Var.Set.union vars (vars_from_sub env target)
                  | _ -> vars
                end
              | Indirect _ -> vars
            end
          | _ -> vars
        in
        Var.Set.union vars (Jmp.free_vars jmp)
    end)
  in
  visitor#visit_sub t vars

let get_vars (env : Env.t) (t : Sub.t) : Var.Set.t =
  let gprs = Env.get_gprs env in
  let mem = Var.Set.singleton (Env.get_mem env) in
  let sp = Var.Set.singleton (Env.get_sp env) in
  let sub_vars = vars_from_sub env t in
  Var.Set.union_list [gprs; mem; sp; sub_vars]

let spec_verifier_error (sub : Sub.t) (_ : Theory.target) : Env.fun_spec option =
  let is_verifier_error name = String.(
      name = "__VERIFIER_error" ||
      name = "__assert_fail")
  in
  if is_verifier_error (Sub.name sub) then
    Some {
      spec_name = "spec_verifier_error";
      spec = Summary (fun env _ _ ->
          let pre =
            Env.get_context env
            |> Bool.mk_false
            |> Constr.mk_goal "assert_fail"
            |> Constr.mk_constr
          in
          pre, env
        )
    }
  else
    None

let spec_verifier_assume (sub : Sub.t) (_ : Theory.target) : Env.fun_spec option =
  if String.equal (Sub.name sub) "__VERIFIER_assume" then
    Some {
      spec_name = "spec_verifier_assume";
      spec = Summary
          (fun env post tid ->
             let ctx = Env.get_context env in
             let post = set_fun_called post env tid in
             let post, env = increment_stack_ptr post env in
             let args = Term.enum arg_t sub in
             let is_input arg =
               match Arg.intent arg with
               | Some In | Some Both -> true
               | _ -> false
             in
             let input =
               match Seq.find args ~f:is_input with
               | Some i -> i
               | None -> failwith "Verifier headerfile must be specified with --api-path" in
             let v = var_of_arg_t input in
             let z3_v, env = Env.get_var env v in
             let size = BV.get_size (Expr.get_sort z3_v) in
             let assumption =
               bv_to_bool z3_v ctx size
               |> Constr.mk_goal (Format.sprintf "assume %s" (Expr.to_string z3_v))
               |> Constr.mk_constr
             in
             Constr.mk_clause [assumption] [post], env)
    }
  else
    None

let spec_verifier_nondet (sub : Sub.t) (_ : Theory.target) : Env.fun_spec option =
  let is_nondet name = String.(
      (is_prefix name ~prefix:"__VERIFIER_nondet_")
      || (equal name "calloc")
      || (equal name "malloc"))
  in
  if is_nondet (Sub.name sub) then
    Some {
      spec_name = "spec_verifier_nondet";
      spec = Summary
          (fun env post tid ->
             let post = set_fun_called post env tid in
             let post, env = increment_stack_ptr post env in
             let args = Term.enum arg_t sub in
             let is_output arg =
               match Arg.intent arg with
               | Some Out | Some Both -> true
               | _ -> false
             in
             let output =
               match Seq.find args ~f:is_output with
               | Some o -> o
               | None -> failwith "Verifier headerfile must be specified with --api-path" in
             let vars = output |> Bap.Std.Arg.rhs |> Exp.free_vars in
             let name = Format.sprintf "%s_ret_%s" (Sub.name sub) in
             Env.freshen ~name post env vars)
    }
  else
    None

let spec_empty (sub : Sub.t) (_ : Theory.target) : Env.fun_spec option =
  if (Seq.is_empty @@ Term.enum blk_t sub) then
    Some {
      spec_name = "spec_empty";
      spec = Summary (fun env post _tid -> post, env)
    }
  else None

let spec_arg_terms (sub : Sub.t) (_ : Theory.target) : Env.fun_spec option =
  let args = Term.enum arg_t sub in
  if not (Seq.is_empty args) then
    Some {
      spec_name = "spec_arg_terms";
      spec = Summary
          (fun env post tid ->
             let post = set_fun_called post env tid in
             let post, env = increment_stack_ptr post env in
             let inputs, outputs = Seq.fold args ~init:([], [])
                 ~f:(fun (ins, outs) arg ->
                     let var = var_of_arg_t arg in
                     match Arg.intent arg with
                     | Some In -> var :: ins, outs
                     | Some Out -> ins, var :: outs
                     | Some Both -> var :: ins, var :: outs
                     | None -> ins, outs)
             in
             let inputs = if Env.use_input_regs env then inputs else [] in
             subst_fun_outputs env sub post ~inputs:inputs ~outputs:outputs)
    }
  else
    None

let spec_rax_out (sub : Sub.t) (target : Theory.target) : Env.fun_spec option =
  (* Calling convention for x86 uses EAX as output register. x86_64 uses RAX. *)
  let defs sub =
    Term.enum blk_t sub
    |> Seq.map ~f:(Term.enum def_t)
    |> Seq.concat
  in
  let is_rax def =
    let reg = Var.to_string (Def.lhs def) in
    String.(reg = "RAX" || reg = "EAX")
  in
  if Seq.exists (defs sub) ~f:is_rax then
    (* RAX is a register that is used in the subroutine *)
    Some {
      spec_name = "spec_rax_out";
      spec = Summary
          (fun env post tid ->
             let post = set_fun_called post env tid in
             let post, env = increment_stack_ptr post env in
             let inputs = if Env.use_input_regs env then input_regs target else [] in
             let rax = Seq.find_exn (defs sub) ~f:is_rax |> Def.lhs in
             subst_fun_outputs env sub post ~inputs ~outputs:[rax])
    }
  else
    None

let spec_chaos_rax (sub : Sub.t) (target : Theory.target) : Env.fun_spec option =
  if is_amd64 target then
    Some {
      spec_name = "spec_chaos_rax";
      spec = Summary
          (fun env post tid ->
             let post = set_fun_called post env tid in
             let post, env = increment_stack_ptr post env in
             let inputs = if Env.use_input_regs env then input_regs target else [] in
             subst_fun_outputs env sub post ~inputs ~outputs:[X86_cpu.AMD64.rax])
    }
  else
    None

let spec_chaos_caller_saved (sub : Sub.t) (target : Theory.target) : Env.fun_spec option =
  Some {
    spec_name = "spec_chaos_caller_saved";
    spec = Summary
        (fun env post tid ->
           let post = set_fun_called post env tid in
           let post, env = increment_stack_ptr post env in
           let inputs = if Env.use_input_regs env then input_regs target else [] in
           let regs = caller_saved_regs target in
           subst_fun_outputs env sub post ~inputs ~outputs:regs)
  }

let spec_afl_maybe_log (sub : Sub.t) (target : Theory.target) : Env.fun_spec option =
  if String.equal (Sub.name sub) "__afl_maybe_log" then
    begin
      if is_amd64 target then
        Some {
          spec_name = "spec_afl_maybe_log";
          spec = Summary
              (fun env post tid ->
                 let post = set_fun_called post env tid in
                 let post, env = increment_stack_ptr post env in
                 let inputs = if Env.use_input_regs env then input_regs target else [] in
                 let outputs =
                   let open X86_cpu.AMD64 in
                   [rax; rcx; rdx]
                 in
                 subst_fun_outputs env sub post ~inputs ~outputs)
        }
      else
        raise (Not_implemented "spec_afl_maybe_log: The spec for afl_maybe_log only \
                                supports x86_64.")
    end
  else
    None

let spec_default (_ : Sub.t) (_ : Theory.target) : Env.fun_spec =
  {
    spec_name = "spec_default";
    spec = Summary (fun env post tid ->
        let post = set_fun_called post env tid in
        increment_stack_ptr post env)
  }

let spec_inline (to_inline : Sub.t Seq.t) (sub : Sub.t) (_ : Theory.target)
  : Env.fun_spec option =
  if Seq.mem to_inline sub ~equal:Sub.equal then
    Some {
      spec_name = "spec_inline";
      spec = Inline
    }
  else
    None

let indirect_spec_default : Env.indirect_spec =
  (* NOTE we keep around exp for that point in the future
   * when we can use it to determine the destination of the
   * indirect call. *)
  fun env post _exp has_return ->
  if has_return then increment_stack_ptr post env
  else post, env

let jmp_spec_default : Env.jmp_spec =
  fun _ _ _ _ -> None

let int_spec_default : Env.int_spec =
  fun env post _ ->
  error "Currently we do not handle system calls%!";
  post, env

let num_unroll : int ref = ref 5

let default_stack_range : Env.mem_range = {
  base_addr = 0x40000000;
  size = 0x800000
}

(* TODO: The default data section range should not be hardcoded as it currently is.
   We should use [brk] to determine this. *)
let default_data_section_range : Env.mem_range = {
  base_addr = 0x000000;
  size = 0x800000
}

(* Determines the condition for taking a jump, and uses it to generate the jump
   expression's precondition based off of the postcondition and the
   precondition of the jump's target. *)
let conditional_jmp (jmp : Jmp.t) (env : Env.t) (target_pre : Constr.t)
    (post : Constr.t) : Constr.t * Env.t =
  let ctx = Env.get_context env in
  let cond = Jmp.cond jmp in
  let cond_val, hooks, env = exp_to_z3 cond env in
  debug "\n\nJump when %s:\n%s\n%!"
    (Expr.to_string cond_val) (hooks_to_string hooks);
  let cond_size = BV.get_size (Expr.get_sort cond_val) in
  let false_cond = Bool.mk_eq ctx cond_val (z3_expr_zero ctx cond_size) in
  let is_unconditional =
    match cond with
    | Bil.Types.Int w -> Word.is_one w
    | _ -> false
  in
  let ite =
    if is_unconditional then
      target_pre
    else
      Constr.mk_ite jmp (Bool.mk_not ctx false_cond) target_pre post
  in
  (* If we add a PC variable, we should separate the befores and afters
     similarly to how we did in visit_def *)
  let vcs = hooks.verify_before @ hooks.verify_after in
  let assume = hooks.assume_before @ hooks.assume_after in
  let post = ite :: vcs in
  Constr.mk_clause assume post, env

let visit_jmp (env : Env.t) (post : Constr.t) (jmp : Jmp.t) : Constr.t * Env.t =
  let jmp_spec = Env.get_jmp_handler env in
  match jmp_spec env post (Term.tid jmp) jmp with
  | Some p_env -> p_env
  | None ->
    let target_pre, env =
      match Jmp.kind jmp with
      | Goto l ->
        begin
          match l with
          | Direct tid ->
            begin
              debug "Goto direct label: %s%!" (Label.to_string l);
              match Env.get_precondition env tid with
              | Some pre -> pre, env
              (* We always hit this point when finish a loop unrolling *)
              | None ->
                error "Precondition for node %s not found!" (Tid.to_string tid);
                failwith ("Error in visit_jmp: \
                           The loop handler should have added the precondition for the node");
            end
          (* TODO: evaluate the indirect jump and
             enumerate the possible concrete values, relate to tids
             (probably tough...) *)
          | Indirect _ ->
            warning "Making an indirect jump, using the default postcondition!\n%!";
            post, env
        end
      | Call call -> visit_call call post env
      (* TODO: do something here? *)
      | Ret l ->
        debug "Return to: %s%!" (Label.to_string l);
        post, env
      (* FIXME: do something here *)
      | Int (i, tid) ->
        debug "Interrupt %d with return to %s%!" i (Tid.to_string tid);
        let ret_pre = Env.get_precondition env tid |>
                      Option.value_exn ?here:None ?error:None ?message:None in
        let handler = Env.get_int_handler env in
        handler env ret_pre i
    in
    conditional_jmp jmp env target_pre post

let visit_elt (env : Env.t) (post : Constr.t) (elt : Blk.elt) : Constr.t * Env.t =
  match elt with
  | `Def def ->
    let var = Def.lhs def in
    let rhs = Def.rhs def in
    let rhs_exp, hooks, env = exp_to_z3 rhs env in
    let z3_var, env = Env.get_var env var in
    debug "Visiting def:\nlhs = %s : <%d>    rhs = %s : <%d>%!"
      (Expr.to_string z3_var) (var |> Var.typ |> typ_size)
      (Expr.to_string rhs_exp) (rhs |> Type.infer_exn |> typ_size);
    (* Adding the specified assumptions and VCs to the postcondition before applying
       the substitution. *)
    let post = post :: hooks.verify_before in
    let post = Constr.mk_clause hooks.assume_before post in
    let post = Constr.substitute_one post z3_var rhs_exp in
    (* Adding the specified assumptions and VCs to the postcondition after applying
       the substitution. *)
    let post = post :: hooks.verify_after in
    let post = Constr.mk_clause hooks.assume_after post in
    post, Env.add_var env var z3_var
  | `Jmp jmp ->
    visit_jmp env post jmp
  | `Phi _ ->
    error "We do not currently handle Phi nodes.\n%!";
    raise (Not_implemented "visit_elt: case `Phi(phi) not implemented")

let visit_block (env : Env.t) (post : Constr.t) (blk : Blk.t) : Constr.t * Env.t =
  debug "Visiting block:\n%s%!" (Blk.to_string blk);
  let compute_pre b =
    Seq.fold b ~init:(post, env) ~f:(fun (pre, env) a -> visit_elt env pre a)
  in
  let pre, env = blk |> Blk.elts ~rev:true |> compute_pre in
  (pre, Env.add_precond env (Term.tid blk) pre)

(* Returns [true] if the node is not reachable from the start of the graph.
   This is used to prune non-reachable subgraphs from the DFS. *)
let unreachable_from_start (graph : Graphs.Ir.t) (start : Graphs.Ir.Node.t)
    (node : Graphs.Ir.Node.t) : bool =
  not (Graphlib.is_reachable (module Graphs.Ir) graph start node)

(* If you skip a node for which another node needs the prcondition, this
   function may fail. *)
let visit_graph (env : Env.t) (post : Constr.t)
    ~(start : Graphs.Ir.Node.t) ~(skip_node : Graphs.Ir.Node.t -> bool)
    (g : Graphs.Ir.t) : Constr.t * Env.t =
  let module G = Graphs.Ir in
  let module Filtered_graph = (val Graphlib.filtered (module G) ~skip_node ()) in
  let leave_node _ n (_, env) =
    let b = G.Node.label n in
    visit_block env post b in
  (* This function is the identity on forward & cross edges, and
     invokes loop handling code on back edges *)
  let enter_edge kind e (_, env) : Constr.t * Env.t =
    match kind with
    | `Back ->
      begin
        let src = G.Edge.src e in
        let dst = G.Edge.dst e in
        debug "Entering back edge from\n%sto\n%s\n%!"
          (G.Node.to_string src) (G.Node.to_string dst);
        let tid = dst |> G.Node.label |> Term.tid in
        match Env.get_precondition env tid with
        | Some pre -> pre, env
        | None ->
          let handler = Env.get_loop_handler env in
          post, handler env post ~start:dst g
      end
    | _ ->
      (* We return postcondition for the entire graph rather than the
         postcondition for a single block. *)
      post, env
  in
  Graphlib.depth_first_search (module Filtered_graph)
    ~enter_edge:enter_edge ~start:start ~leave_node:leave_node ~init:(post, env)
    g

(* BAP currently doesn't have a way to determine that exit does not return.
   This function removes the backedge after the call to exit. *)
let filter (env : Env.t) (calls : string list) (cfg : Graphs.Ir.t) : Graphs.Ir.t =
  let enter_edge kind e cfg =
    match kind with
    | `Back -> begin
        let elts =
          e
          |> Graphs.Ir.Edge.src
          |> Graphs.Ir.Node.label
          |> Blk.elts ~rev:true
        in
        let call_target = Seq.find_map elts ~f:(function
            | `Jmp j -> begin
                match Jmp.kind j with
                | Call c -> begin
                    match Call.target c with
                    | Direct tid -> begin
                        match Env.get_sub_name env tid with
                        | Some target -> List.find calls ~f:(String.equal target)
                        | None -> None
                      end
                    | _ -> None
                  end
                | _ -> None
              end
            | _ -> None)
        in
        match call_target with
        | Some c ->
          info "Removing the back edge from the return from %s" c;
          Graphs.Ir.Edge.remove e cfg
        | None -> cfg
      end
    | _ -> cfg
  in
  Graphlib.depth_first_search (module Graphs.Ir) ~enter_edge:enter_edge ~init:cfg cfg

let visit_sub (env : Env.t) (post : Constr.t) (sub : Sub.t) : Constr.t * Env.t =
  let sub_name = (Sub.to_string sub) in
  debug "Visiting sub:\n%s%!" sub_name;
  let pre, env' =
    if (Seq.is_empty @@ Term.enum blk_t sub)
    then
      (
        warning "encountered empty subroutine %s%!" sub_name;
        (post, env)
      )
    else
      let cfg = sub |> Sub.to_cfg |> filter env ["exit"] in
      let start = Term.first blk_t sub
                  |> Option.value_exn ?here:None ?error:None ?message:None
                  |> Graphs.Ir.Node.create in
      visit_graph ~start ~skip_node:(unreachable_from_start cfg start) env post cfg
  in (pre, Env.add_precond env' (Term.tid sub) pre)

(* Replace the [inline_func] placeholder with [visit_sub]. *)
let _  = inline_func :=
    fun post env tid ->
      let subs = Env.get_subs env in
      let target_sub = Seq.find_exn subs ~f:(fun s -> Tid.equal (Term.tid s) tid) in
      let post = set_fun_called post env tid in
      visit_sub env post target_sub

(* Creates the z3_expr (not (= addr null)) *)
let non_null_expr (env : Env.t) (addr : Exp.t) : Constr.z3_expr =
  let ctx = Env.get_context env in
  let width = match Type.infer_exn addr with
    | Imm n -> n
    | Mem _ ->
      let err_msg = Format.sprintf "Error in non_null_expr: %s is a memory read \
                                    instead of a word" (Exp.to_string addr) in
      error "%s" err_msg;
      failwith err_msg
    | Unk ->
      let err_msg = Format.sprintf "Error in non_null_expr: %s is of Unknown type"
          (Exp.to_string addr) in
      error "%s" err_msg;
      failwith err_msg
  in
  let null = BV.mk_numeral ctx "0" width in
  let addr_val,_,_ = exp_to_z3 addr env in
  Bool.mk_not ctx (Bool.mk_eq ctx null addr_val)

let collect_non_null_loads (env : Env.t) (exp : Exp.t) : Constr.z3_expr list =
  let visitor =
    object inherit [Constr.z3_expr list] Exp.visitor
      method! visit_load ~mem:_ ~addr:addr _ _ conds =
        (non_null_expr env addr) :: conds
    end
  in
  visitor#visit_exp exp []

let collect_non_null_stores (env : Env.t) (exp : Exp.t) : Constr.z3_expr list =
  let visitor =
    object inherit [Constr.z3_expr list] Exp.visitor
      method! visit_store ~mem:_ ~addr:addr ~exp:_ _ _ conds =
        (non_null_expr env addr) :: conds
    end
  in
  visitor#visit_exp exp []

let jmp_spec_reach (m : bool Jmp.Map.t) : Env.jmp_spec =
  let is_goto jmp = match Jmp.kind jmp with Goto _ -> true | _ -> false in
  Jmp.Map.fold m ~init:jmp_spec_default
    ~f:(fun ~key ~data spec ->
        fun env post tid jmp ->
          if Jmp.(key <> jmp) || not (is_goto jmp) then
            spec env post tid jmp
          else
            begin
              match Jmp.kind jmp with
              | Goto l ->
                begin
                  match l with
                  | Direct tid ->
                    debug "Goto direct label: %s%!" (Label.to_string l);
                    let l_pre =
                      match Env.get_precondition env tid with
                      | Some pre -> pre
                      (* We always hit this point when finish a loop unrolling *)
                      | None ->
                        info "Precondition for node %s not found!" (Tid.to_string tid);
                        post
                    in
                    let ctx = Env.get_context env in
                    let cond = Jmp.cond jmp in
                    let cond_val, hooks, env = exp_to_z3 cond env in
                    debug "\n\nJump when %s:\n%s\n%!"
                      (Expr.to_string cond_val) (hooks_to_string hooks);
                    let cond_size = BV.get_size (Expr.get_sort cond_val) in
                    let false_cond = Bool.mk_eq ctx cond_val (z3_expr_zero ctx cond_size) in
                    let constr = if data then
                        [Bool.mk_not ctx false_cond
                         |> Constr.mk_goal (Expr.to_string cond_val)
                         |> Constr.mk_constr;
                         l_pre]
                      else
                        [false_cond
                         |> Constr.mk_goal (Expr.to_string false_cond)
                         |> Constr.mk_constr;
                         post]
                    in
                    let assume = hooks.assume_before @ hooks.assume_after in
                    let vcs = hooks.verify_before @ hooks.verify_after in
                    let post = constr @ vcs in
                    Some (Constr.mk_clause assume post, env)
                  | Indirect _ -> None
                end
              | _ -> assert false
            end)

(* This adds a non-null condition for every memory read in the term *)
let non_null_load_vc : Env.exp_cond = fun env exp ->
  let ctx = Env.get_context env in
  let conds = collect_non_null_loads env exp in
  if List.is_empty conds then
    None
  else
    Some (Verify (BeforeExec (Constr.mk_goal "verify non-null mem load"
                                (Z3_utils.mk_and ctx conds))))

let non_null_load_assert : Env.exp_cond = fun env exp ->
  let ctx = Env.get_context env in
  let conds = collect_non_null_loads env exp in
  if List.is_empty conds then
    None
  else
    Some (Assume (BeforeExec (Constr.mk_goal "assume non-null mem load"
                                (Z3_utils.mk_and ctx conds))))

(* This adds a non-null condition for every memory write in the term *)
let non_null_store_vc : Env.exp_cond = fun env exp ->
  let ctx = Env.get_context env in
  let conds = collect_non_null_stores env exp in
  if List.is_empty conds then
    None
  else
    Some (Verify (BeforeExec (Constr.mk_goal "verify non-null mem store"
                                (Z3_utils.mk_and ctx conds))))

let non_null_store_assert : Env.exp_cond = fun env exp ->
  let ctx = Env.get_context env in
  let conds = collect_non_null_stores env exp in
  if List.is_empty conds then
    None
  else
    Some (Assume (BeforeExec (Constr.mk_goal "assume non-null mem store"
                                (Z3_utils.mk_and ctx conds))))

(* For a given address, generates the constraint of:
   addr >= RSP \/ addr <= stack_bottom - 0x256 *)
let in_valid_mem_region (env : Env.t) (addr : Constr.z3_expr) : Constr.z3_expr =
  (* NOTE: we are assuming stack grows down.*)
  let ctx = Env.get_context env in
  (* We are hardcoding the heap to be 0x256 bytes beneath the bottom of the
     stack. *)
  let stack_end = (Env.get_stack_end env) - 0x256 in
  let width = env |> Env.get_sp |> Var.typ |> typ_size in
  let sb_bv = BV.mk_numeral ctx (Int.to_string stack_end) width in
  let stack_pointer, _ = Env.get_var env (Env.get_sp env) in
  (* addr >= RSP *)
  let uge = BV.mk_uge ctx addr stack_pointer in
  (* addr <= stack_bottom - 0x256 *)
  let ule = BV.mk_ule ctx addr sb_bv in
  (* addr >= RSP \/ addr <= stack_bottom - 0x256 *)
  Bool.mk_or ctx [uge; ule]

(* At every memory load, add a constraint that the address is in a valid
   location in memory. *)
let collect_valid_mem_loads (env : Env.t) (exp : Exp.t) : Constr.z3_expr list =
  let visitor =
    object inherit [Constr.z3_expr list] Exp.visitor
      method! visit_load ~mem:_ ~addr:addr _ _ conds =
        let addr_val, _, _ = exp_to_z3 addr env in
        (in_valid_mem_region env addr_val) :: conds
    end
  in
  visitor#visit_exp exp []

(* At every memory store, add a constraint that the address is in a valid
   location in memory. *)
let collect_valid_mem_stores (env : Env.t) (exp : Exp.t) : Constr.z3_expr list =
  let visitor =
    object inherit [Constr.z3_expr list] Exp.visitor
      method! visit_store ~mem:_ ~addr:addr ~exp:_ _ _ conds =
        let addr_val, _, _ = exp_to_z3 addr env in
        (in_valid_mem_region env addr_val) :: conds
    end
  in
  visitor#visit_exp exp []

(* Adds a VC for the constraints found by the [collector] tagged with a [name]. *)
let valid_mem_vc (collector : Env.t -> Exp.t -> Constr.z3_expr list) (name : string)
  : Env.exp_cond = fun env exp ->
  let ctx = Env.get_context env in
  let conds = collector env exp in
  if List.is_empty conds then
    None
  else
    Some (Verify (BeforeExec (Constr.mk_goal name (Bool.mk_and ctx conds))))

(* Adds an assumption for the constraints found by the [collector] tagged with
   a [name]. *)
let valid_mem_assert (collector : Env.t -> Exp.t -> Constr.z3_expr list) (name : string)
  : Env.exp_cond = fun env exp ->
  let ctx = Env.get_context env in
  let conds = collector env exp in
  List.iter conds ~f:(fun c ->
      if Bool.is_false c then
        warning "The assumption %s is false! This may result in a false UNSAT.%!"
          (Expr.to_string c)
      else ());
  if List.is_empty conds then
    None
  else
    Some (Assume (BeforeExec (Constr.mk_goal name (Bool.mk_and ctx conds))))

(* Verifies that a memory load is in a valid location in memory in the modified
   binary. *)
let valid_load_vc : Env.exp_cond =
  valid_mem_vc collect_valid_mem_loads "verify valid mem load"

(* Assumes that a memory load is in a valid location in memory in the original
   binary. *)
let valid_load_assert : Env.exp_cond =
  valid_mem_assert collect_valid_mem_loads "assume valid mem load"

(* Verifies that a memory store is in a valid location in memory in the modified
   binary. *)
let valid_store_vc : Env.exp_cond =
  valid_mem_vc collect_valid_mem_stores "verify valid mem store"

(* Assumes that a memory store is in a valid location in memory in the original
   binary. *)
let valid_store_assert : Env.exp_cond =
  valid_mem_assert collect_valid_mem_stores "assume valid mem store"

(* At a memory read, add two assumptions of the form:
   Data(x)  => init_mem_orig[x] == init_mem_mod[x + d] and
   Stack(x) => init_mem_orig[x] == init_mem_mod[x] *)
let collect_mem_read_expr (env1 : Env.t) (env2 : Env.t) (exp : Exp.t)
    (offset : Constr.z3_expr -> Constr.z3_expr) : Constr.z3_expr list =
  let ctx = Env.get_context env1 in
  let bap_mem1 = Env.get_mem env1 in
  let bap_mem2 = Env.get_mem env2 in
  let visitor =
    begin
      object inherit [Constr.z3_expr list] Exp.visitor
        method! visit_load ~mem:_ ~addr:addr endian size conds =
          let addr, _, _ = exp_to_z3 addr env1 in
          let word_size = Size.in_bits size in
          let compare_mem addr1 addr2 =
            let init_mem1 = Option.value_exn (Env.get_init_var env1 bap_mem1) in
            let init_mem2 = Option.value_exn (Env.get_init_var env2 bap_mem2) in
            let mem_orig = load_z3_mem ctx ~word_size ~mem:init_mem1 ~addr:addr1 endian in
            let mem_mod = load_z3_mem ctx ~word_size ~mem:init_mem2 ~addr:addr2 endian in
            Bool.mk_eq ctx mem_orig mem_mod
          in
          let mem_eq_offset = compare_mem addr (offset addr) in
          let mem_eq = compare_mem addr addr in
          let constr =
            Bool.mk_ite ctx (Env.in_stack env1 addr) mem_eq
              (Bool.mk_ite ctx (Env.in_data_section env1 addr) mem_eq_offset
                 mem_eq)
          in
          debug "Adding assumptions:\n%s\n%!"
            (Expr.to_string (Expr.simplify constr None));
          constr :: conds
      end
    end
  in
  visitor#visit_exp exp []

let init_vars (vars : Var.Set.t) (env : Env.t) : Constr.t list * Env.t =
  let ctx = Env.get_context env in
  Var.Set.fold vars ~init:([], env)
    ~f:(fun (inits, env) v ->
        let z3_v, env = Env.get_var env v in
        let init_v, env = Env.mk_init_var env v in
        let comp =
          Bool.mk_eq ctx z3_v init_v
          |> Constr.mk_goal
            (Format.sprintf "%s = %s" (Expr.to_string z3_v) (Expr.to_string init_v))
          |> Constr.mk_constr
        in
        debug "Initializing var: %s\n%!" (Constr.to_string comp);
        comp :: inits, env)


let init_mem (env : Env.t) (mem : value memmap) : Constr.t list * Env.t =
  let mem_var = Env.get_mem env in
  let z3_mem, env = Env.get_var env mem_var in
  let bitv_pairs =
    mem |> Memmap.filter ~f:(fun v ->
        match Value.get Image.section v with
        | None -> false
        | Some name -> String.equal name ".rodata") |>
    Memmap.to_sequence |>
    Seq.fold ~init:[] ~f:(fun pairs (mem, _) ->
        Memory.foldi mem ~init:pairs
          ~f:(fun addr content pairs ->
            (addr, content)::pairs))
  in
  let z3_ctxt = Env.get_context env in
  let mem_assoc (addr, word) =
    let addr = word_to_z3 z3_ctxt addr in
    let word = word_to_z3 z3_ctxt word in
    (* z3_mem[addr] == word *)
    Bool.mk_eq z3_ctxt (Z3Array.mk_select z3_ctxt z3_mem addr) word
  in
  let z3_assoc = List.map ~f:mem_assoc bitv_pairs in
  let mk_cstr b = b |> Constr.mk_goal ".rodata_init" |> Constr.mk_constr in
  info "Initializing values in %a\n%!" Var.pp mem_var;
  (List.map ~f:mk_cstr z3_assoc, env)


(* Builds a spec of the form (sub_pre /\ (sub_post => post) where post
   is the spec right before the subroutine call. All physical registers and mem
   in post and sub_post are replaced with fresh Z3 functions, and init- physical
   registers/init-mem in sub_post are replaced with regular registers/mem.
   This is only applied for subroutines with the name sub_name. *)
let user_func_spec
    ~sub_name:(sub_name : string)
    ~sub_pre:(sub_pre : string)
    ~sub_post:(sub_post : string)
    (sub : Sub.t)
    (_ : Theory.target)
  : Env.fun_spec option =
  debug "Making user-defined subroutine spec with subroutine-name: %s, pre:
%s, post: %s \n%!" sub_name sub_pre sub_post;
  if String.equal sub_name (Sub.name sub) then
    let spec env post tid = (
      (* turn strings into proper smtlib2 statements; incr stack_ptr *)
      let sub_pre : Constr.t = Z3_utils.mk_smtlib2_single env sub_pre in
      let sub_post : Constr.t = Z3_utils.mk_smtlib2_single env sub_post in
      let sub_post, env = increment_stack_ptr sub_post env in
      (* collect (physical) inputs/outputs of sub *)
      let sub_inputs : Var.t list = vars_from_sub env sub |> Var.Set.to_list in
      let sub_inputs =
        List.filter sub_inputs ~f:(fun v -> Var.is_physical v) in
      let sub_outputs : Var.t list = sub_inputs in
      let vars = Set.add (Env.get_gprs env) (Env.get_mem env)
                 |> Var.Set.to_list in
      let regs = List.map vars ~f:(fun v -> let r,_ = Env.get_var env v in r) in
      let inits = List.map vars ~f:(fun v ->
          let r  = Env.get_init_var env v in
          match r with
          | Some q -> q
          | None -> let q, _ = Env.mk_init_var env v in q) in
      let tid_name : string = Tid.name tid in
      let sub_post, env = subst_fun_outputs ~tid_name:tid_name env sub
          sub_post ~inputs:sub_inputs ~outputs:sub_outputs in
      (* replace init-vars with vars inside sub_post *)
      let sub_post = Constr.substitute sub_post inits regs in
      (*combine sub_post and post*)
      let post, env = subst_fun_outputs ~tid_name:tid_name env sub
          post ~inputs:sub_inputs ~outputs:sub_outputs in
      let sub_post_imp_post : Constr.t =
        Constr.mk_clause [sub_post] [post] in
      (* combine pre and post *)
      let result : Constr.t = Constr.mk_clause [] [sub_pre ; sub_post_imp_post] in
      result, env)
    in
    Some {
      spec_name = "user_func_spec";
      spec = (Summary spec)}
  else None

(* The exp_cond to add to the environment in order to invoke the hooks regarding
   memory read offsets. *)
let mem_read_offsets (env2 : Env.t) (offset : Constr.z3_expr -> Constr.z3_expr)
  : Env.exp_cond =
  fun env1 exp ->
  let ctx = Env.get_context env1 in
  let conds = collect_mem_read_expr env1 env2 exp offset in
  let name = "Assume memory equivalence at offset" in
  if List.is_empty conds then
    None
  else
    Some (Assume (AfterExec (Constr.mk_goal name (Z3_utils.mk_and ctx conds))))

let check ?(refute = true) ?(print_constr = []) ?(debug = false) ?ext_solver
    ?(fmt = Format.err_formatter) (solver : Solver.solver)
    (ctx : Z3.context) (pre : Constr.t)  : Solver.status =
  Format.fprintf fmt "Evaluating precondition.\n%!";

  if (List.mem print_constr "precond-internal" ~equal:(String.equal)) then (
    let colorful = List.mem print_constr "colorful" ~equal:String.equal in
    Printf.printf "Internal : %s \n %!" (Constr.to_string ~colorful:colorful pre) ) ;
  let pre' = Constr.eval ~debug:debug pre ctx in
  Format.fprintf fmt "Checking precondition with Z3.\n%!";
  let is_correct =
    if refute then
      Bool.mk_implies ctx pre' (Bool.mk_false ctx)
    else
      pre'
  in
  Z3.Solver.add solver [is_correct];
  if (List.mem print_constr "precond-smtlib" ~equal:(String.equal)) then (
    Printf.printf "Z3 : \n %s \n %!" (Z3.Solver.to_string solver) );
  match ext_solver with
  | None -> Z3.Solver.check solver []
  | Some (solver_path, declsyms) ->
    Z3_utils.check_external solver solver_path ctx declsyms

let exclude ?fmt:(fmt = Format.err_formatter) (solver : Solver.solver)
    (ctx : Z3.context) ~var:(var : Constr.z3_expr) ~pre:(pre : Constr.t)
  : Solver.status =
  let model = Constr.get_model_exn solver in
  let value = Constr.eval_model_exn model var in
  let cond = Bool.mk_not ctx (Bool.mk_eq ctx var value) in
  Solver.push solver;
  Solver.add solver [cond];
  info "Added constraints: %s\n%!"
    (Solver.get_assertions solver |> List.to_string ~f:Expr.to_string);
  check ~fmt:fmt solver ctx pre

let set_of_reg_names (env : Env.t) (t : Sub.t) (var_names : string list) : Var.Set.t =
  let all_vars = get_vars env t in
  let has_name name var = String.equal name (Var.to_string var) in
  List.fold var_names ~init:Var.Set.empty ~f:(fun vars name ->
      match Var.Set.find all_vars ~f:(has_name name) with
      | Some v -> Var.Set.add vars v
      | None ->
        warning "%s not in sub and will not be added to the postcondition" name;
        vars
    )

let set_sp_range (env : Env.t) : Constr.t =
  let sp, _ = Env.get_var env (Env.get_sp env) in
  let stack_range = Env.init_stack_ptr env sp in
  stack_range
  |> Constr.mk_goal (Format.sprintf "SP in stack range: %s" (Expr.to_string stack_range))
  |> Constr.mk_constr

let construct_pointer_constraint (l_orig : Constr.z3_expr list) (env1 : Env.t)
    (l_mod : (Constr.z3_expr list) option) (env2: Env.t option) : Constr.t =
  let ctx = Env.get_context env1 in
  let gen_constr, l = match l_mod, env2 with
    (* comparative case *)
    | Some l_mod, Some env2 ->
      (* Encode constraint that each register is not within stack*)
      (fun acc (reg_orig, reg_mod) ->
         let is_valid_orig = in_valid_mem_region env1 reg_orig in
         let is_valid_mod = in_valid_mem_region env2 reg_mod in
         (* (reg_orig >= RSP \/ reg_orig <= stack_bottom) /\
            (reg_mod >= RSP \/ reg_mod <= stack_bottom)     *)
         let and_c = Bool.mk_and ctx [is_valid_orig; is_valid_mod] in
         Bool.mk_and ctx [and_c; acc]
      ), List.zip_exn l_orig l_mod
    (* single binary case *)
    | _, _ ->
      (fun acc (reg, _) ->
         (* reg >= RSP \/ reg <= stack_bottom *)
         let constr = in_valid_mem_region env1 reg in
         Bool.mk_and ctx [constr; acc]
      ), List.zip_exn l_orig l_orig
  in
  let expr = List.fold l ~init:(Bool.mk_true ctx) ~f:gen_constr in
  Constr.mk_goal "pointer_precond" expr |> Constr.mk_constr

(* Checks if [tid] corresponds to the tid of a block in a loop. *)
let in_loop (loop : Graphs.Ir.Node.t group) (tid : Tid.t) : bool =
  Seq.exists (Group.enum loop) ~f:(fun n ->
      Tid.equal (n |> Graphs.Ir.Node.label |> Term.tid) tid)

(* Looks up the exit node of a loop by:
   - obtaining the post dominator tree
   - for each node in the SCC, find its parent in the dominator tree
   - if the parent node is not in the original SCC, it is an exit node.

   The exit node of a loop is a node outside of the SCC in the control flow
   graph. This node will always be visited when exiting a loop.
*)
let loop_exit (loop : Graphs.Ir.Node.t group) (graph : Graphs.Ir.t)
  : Graphs.Ir.Node.t option =
  let* leaf = Seq.find (Graphlib.postorder_traverse (module Graphs.Ir) graph)
      ~f:(fun n -> Seq.is_empty (Graphs.Ir.Node.succs n graph)) in
  let dom_tree = Graphlib.dominators (module Graphs.Ir) ~rev:true graph leaf in
  Seq.find_map (Group.enum loop) ~f:(fun n ->
      let* parent = Tree.parent dom_tree n in
      if Group.mem loop parent then
        None
      else
        Some parent)

(* Gets the precondition of the exit node of a loop. *)
let exit_pre (env : Env.t) (post : Constr.t) (node : Graphs.Ir.Node.t)
    (g : Graphs.Ir.t) (loop : Graphs.Ir.Node.t group) : Env.t =
  List.fold [loop_exit] ~init:env ~f:(fun e spec ->
      match spec loop g with
      | None -> e
      | Some exit ->
        let skip_node n =
          let label = Graphs.Ir.Node.label n in
          let in_loop = in_loop loop (Term.tid label) in
          let unreachable = unreachable_from_start g node n in
          in_loop || unreachable
        in
        let _, env = visit_graph env post ~start:exit ~skip_node g in
        env)

(* This is the default handler for loops, which unrolls a loop by:
   - Looking at the target node for a backjump
   - If the node has been visited more than [num_unroll] times, use the [loop_exit_pre] precondition
   - Otherwise, decrement the [depth] map which tracks the unrollings for that node *)
let loop_unroll (num_unroll : int) : Env.loop_handler =
  let module Node = Graphs.Ir.Node in
  let find_depth env node =
    Env.get_unroll_depth env (Node.label node)
    |> Option.value ~default:num_unroll
  in
  let decr_depth = function None -> num_unroll - 1 | Some n -> n - 1 in
  let unroll env pre ~start:node g =
    let tid = node |> Node.label |> Term.tid in
    debug "Unrolling loop for %s%!" (Tid.to_string tid);
    if find_depth env node <= 0 then
      let scc = Graphlib.strong_components (module Graphs.Ir) g in
      let loop = Option.value_exn (Partition.group scc node) in
      let env = exit_pre env pre node g loop in
      match Env.get_precondition env tid with
      | Some _ -> env
      | None ->
        warning "Trivial precondition is being used for node %s\n%!"
          (Tid.to_string tid);
        Env.add_precond env tid pre
    else
      begin
        let updated_env = Env.set_unroll_depth env (Node.label node) ~f:decr_depth in
        let _, env = visit_graph updated_env pre
            ~start:node ~skip_node:(unreachable_from_start g node) g in
        env
      end
  in
  unroll

let loop_vars
    ~(start : Graphs.Ir.Node.t)
    ~(skip_node : Graphs.Ir.Node.t -> bool)
    (graph : Graphs.Ir.t)
  : Var.Set.t =
  let module Filtered_graph =
    (val Graphlib.filtered (module Graphs.Ir) ~skip_node ()) in
  let enter_node _ node vars =
    let blk = Graphs.Ir.Node.label node in
    let defs = Term.enum def_t blk in
    Seq.fold defs ~init:vars ~f:(fun vs def ->
        Var.Set.add vs (Def.lhs def))
  in
  Graphlib.depth_first_search (module Filtered_graph)
    ~start ~enter_node ~init:Var.Set.empty graph

let loop_invariant_checker (loop_invariants : Env.loop_invariants) (tid : Tid.t)
  : Env.loop_handler option =
  let* loop_invariant = Tid.Map.find loop_invariants tid in
  Some (fun env post ~start:node g ->
      (* WP(while E do S done, R) *)
      let tid = node |> Graphs.Ir.Node.label |> Term.tid in
      debug "Checking loop invariant for %s%!" (Tid.to_string tid);
      (* I *)
      let name = Format.sprintf "Loop invariant (%s)%!" (Tid.to_string tid) in
      let invariant = Z3_utils.mk_smtlib2_single ~name:(Some name)
          env loop_invariant in
      debug "Loop invariant: %s%!" (Constr.to_string invariant);
      let scc = Graphlib.strong_components (module Graphs.Ir) g in
      let loop = Option.value_exn (Partition.group scc node) in
      let env = Env.add_precond env tid invariant in
      (* forall y, (I => ite(~E, R, WP(S, I)))[x <- y] *)
      let loop_body, env =
        let skip_node n =
          let unreachable = unreachable_from_start g node n in
          let tid = n |> Graphs.Ir.Node.label |> Term.tid in
          let outside_loop = not @@ in_loop loop tid in
          unreachable || outside_loop
        in
        let env = exit_pre env post node g loop in
        let body_wp, env = visit_graph ~start:node ~skip_node env post g in
        let vars = loop_vars ~start:node ~skip_node g in
        let name = Format.sprintf "loop_%s" in
        Env.freshen ~name (Constr.mk_clause [invariant] [body_wp]) env vars
      in
      let pre = Constr.mk_clause [] [invariant; loop_body] in
      Env.add_precond env tid pre)

let mk_env
    ?subs:(subs = Seq.empty)
    ?specs:(specs = [])
    ?default_spec:(default_spec = spec_default)
    ?indirect_spec:(indirect_spec = indirect_spec_default)
    ?jmp_spec:(jmp_spec = jmp_spec_default)
    ?int_spec:(int_spec = int_spec_default)
    ?exp_conds:(exp_conds = [])
    ?loop_handlers:(loop_handlers = [])
    ?default_loop_handler:(default_loop_handler = loop_unroll !num_unroll)
    ?freshen_vars:(freshen_vars = false)
    ?use_fun_input_regs:(use_fun_input_regs = true)
    ?stack_range:(stack_range = default_stack_range)
    ?data_section_range:(data_section_range = default_data_section_range)
    ?func_name_map:(func_name_map = String.Map.empty)
    ?smtlib_compat:(smtlib_compat = false)
    ~target:(target : Theory.target)
    (ctx : Z3.context)
    (var_gen : Env.var_gen)
  : Env.t =
  Env.mk_env
    ~subs
    ~specs
    ~default_spec
    ~indirect_spec
    ~jmp_spec
    ~int_spec
    ~exp_conds
    ~loop_handlers
    ~default_loop_handler
    ~target
    ~freshen_vars
    ~use_fun_input_regs
    ~stack_range
    ~data_section_range
    ~func_name_map
    ~smtlib_compat
    ctx var_gen
