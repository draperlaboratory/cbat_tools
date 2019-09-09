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

include Self()

module Expr = Z3.Expr
module Arith = Z3.Arithmetic
module BV = Z3.BitVector
module Bool = Z3.Boolean
module Array = Z3.Z3Array
module FuncDecl = Z3.FuncDecl
module Env = Environment
module Constr = Constraint

exception Not_implemented of string

let z3_expr_zero (ctx : Z3.context) (size : int) : Constr.z3_expr = BV.mk_numeral ctx "0" size
let z3_expr_one (ctx : Z3.context) (size : int) : Constr.z3_expr = BV.mk_numeral ctx "1" size

let binop (ctx : Z3.context) (b : binop) : Constr.z3_expr -> Constr.z3_expr -> Constr.z3_expr =
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
  | EQ -> fun x y -> Bool.mk_ite ctx (Bool.mk_eq ctx x y) one zero
  | NEQ -> fun x y -> Bool.mk_ite ctx (Bool.mk_eq ctx x y) zero one
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

let lookup_sub (label : Label.t) (post : Constr.t) (env : Env.t) : Constr.t * Env.t =
  match label with
  | Direct tid ->
    begin
      match Env.get_sub_handler env tid with
      | Some (Summary compute_func) -> compute_func env post tid
      | Some Inline -> !inline_func post env tid
      | None -> post, env
    end
  (* TODO: Evaluate the expression for the indirect jump and
   * figure out how to handle this case *)
  | Indirect _ -> post, env

let load_z3_mem (ctx : Z3.context) ~word_size:word_size ~mem:(mem : Constr.z3_expr)
    ~addr:(addr : Constr.z3_expr) (endian : Bap.Std.endian) : Constr.z3_expr =
  assert (Array.is_array mem && mem |> Expr.get_sort
                                |> Array.get_range
                                |> Z3.Sort.get_sort_kind |> (fun s -> s = Z3enums.BV_SORT));
  let m_size = mem |> Expr.get_sort |> Array.get_range |> BV.get_size in
  let addr_size = addr |> Expr.get_sort |> BV.get_size in
  let nums_to_read = word_size / m_size in
  debug "Creating load on Mem<%d,%d>, with target Imm<%d>%!" addr_size m_size word_size;
  assert (nums_to_read > 0);
  let rec read_list n addr reads =
    if n = 0 then reads
    else
      (* TODO: handle overflow *)
      let addr' = BV.mk_add ctx addr (z3_expr_one ctx addr_size) in
      read_list (n-1) addr' (Array.mk_select ctx mem addr :: reads)
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
  assert (Array.is_array mem && mem |> Expr.get_sort
                                |> Array.get_range
                                |> Z3.Sort.get_sort_kind |> (fun s -> s = Z3enums.BV_SORT));
  let m_size = mem |> Expr.get_sort |> Array.get_range |> BV.get_size in
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
        let mem' = Array.mk_store ctx mem addr e_chunk_n in
        let addr' = BV.mk_add ctx addr (z3_expr_one ctx addr_size) in
        store (n-1) (next_loc loc) addr' mem'
      end
  in
  debug "Creating store on Mem<%d,%d>, with target Imm<%d>%!" addr_size m_size word_size;
  store nums_to_write first_loc addr mem

let bv_to_bool (bv : Constr.z3_expr) (ctx : Z3.context) (width : int) : Constr.z3_expr =
  let zero = z3_expr_zero ctx width in
  Bool.mk_not ctx (Bool.mk_eq ctx bv zero)

let exp_to_z3 (exp : Exp.t) (env : Env.t) : Constr.z3_expr * Constr.t list * Constr.t list * Env.t =
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
      let x_val, env = exp_to_z3_body x env in
      let y_val, env = exp_to_z3_body y env in
      let x_size = x_val |> Expr.get_sort |> BV.get_size in
      let y_size = y_val |> Expr.get_sort |> BV.get_size in
      assert (x_size = y_size);
      binop ctx bop x_val y_val, env
    | UnOp (u, x) ->
      debug "Visiting unop: %s %s%!" (Bil.string_of_unop u) (Exp.to_string x);
      let x_val, env = exp_to_z3_body x env in
      unop ctx u x_val, env
    | Var v ->
      debug "Visiting var: %s%!" (Var.to_string v);
      Env.get_var env v
    | Bil.Types.Int w ->
      debug "Visiting int: %s%!" (Word.to_string w);
      let fmt = Format.str_formatter in
      Word.pp_dec fmt w;
      let s = Format.flush_str_formatter () in
      BV.mk_numeral ctx s (Word.bitwidth w), env
    | Cast (cst, i, x) ->
      debug "Visiting cast: %s from %d to %s%!"
        (Bil.string_of_cast cst) i (Exp.to_string x);
      let x_val, env = exp_to_z3_body x env in
      cast ctx cst i x_val, env
    | Let (v, exp, body) ->
      debug "Visiting let %s = %s in %s%!"
        (Var.to_string v) (Exp.to_string exp) (Exp.to_string body);
      let exp_val, env = exp_to_z3_body exp env in
      (* FIXME: we're handling this incorrectly! The variable should
         be removed from the context after leaving the scope of the
         Let! *)
      let env' = Env.add_var env v exp_val in
      exp_to_z3_body body env'
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
  let a, v = Env.mk_exp_conds env exp in
  let assume = List.map a ~f:Constr.mk_constr in
  let verify = List.map v ~f:Constr.mk_constr in
  let z3_exp, new_env = exp_to_z3_body exp env in
  z3_exp, assume, verify, new_env

let set_fun_called (post : Constr.t) (env : Env.t) (tid : Tid.t) : Constr.t =
  let ctx = Env.get_context env in
  let fun_name = Bool.mk_const_s ctx (Env.get_called env tid |>
                                      Option.value_exn ?here:None ?error:None ?message:None) in
  Constr.substitute_one post fun_name (Bool.mk_true ctx)

let get_stack_ptr_offset (sub : Sub.t) (arch : Arch.t) : Exp.t =
  let module Target = (val target_of_arch arch) in
  let blks = Term.to_sequence ~rev:true blk_t sub in
  let ret_block = Seq.find blks ~f:(fun blk ->
      (* Look for the return address, which is the target #x of a call instruction
         of the form: call #x with noreturn *)
      let ret_addr =
        let jmps = Term.to_sequence ~rev:true jmp_t blk in
        Seq.find_map jmps ~f:(fun jmp ->
            match Jmp.kind jmp with
            | Call call -> begin
                match Call.return call with
                | Some _ -> None
                | None ->
                  match Call.target call with
                  | Direct _ -> None
                  | Indirect label ->
                    let label_vars = Exp.free_vars label in
                    match Var.Set.choose label_vars with
                    | None -> None
                    | Some target ->
                      (* In BIR, the return address is stored on the stack and then
                         saved to a virtual variable to pass into the call instruction. *)
                      if Var.Set.length label_vars = 1 && Var.is_virtual target then
                        Some target
                      else
                        None
              end
            | _ -> None)
      in
      (* Check to see if the target value was obtained from the stack,
         i.e. #x := mem[RSP, el]:u64 *)
      match ret_addr with
      | None -> false
      | Some addr ->
        let defs = Term.to_sequence ~rev:true def_t blk in
        Seq.exists defs ~f:(fun def ->
            if Var.equal (Def.lhs def) addr then begin
              match Def.rhs def with
              | Load (_, Var addr, _, _) -> Target.CPU.is_sp addr
              | _ -> false
            end else
              false))
  in
  let sp = Bil.var Target.CPU.sp in
  match ret_block with
  | None ->
    debug "Sub %s has no return" (Sub.name sub);
    sp
  | Some blk ->
    let defs = Term.to_sequence def_t blk in
    Seq.fold defs ~init:sp ~f:(fun offset def ->
        (* Looks for instructions in the form SP := SP +/- offset *)
        if Var.equal (Def.lhs def) Target.CPU.sp then begin
          match Def.rhs def with
          | BinOp (PLUS, Var v, w) ->
            if Var.equal v Target.CPU.sp then
              BinOp (PLUS, offset, w)
            else offset
          | BinOp (MINUS, Var v, w) ->
            if Var.equal v Target.CPU.sp then begin
              warning "Stack pointer in %s is being decremented by %s before return"
                (Sub.name sub) (Exp.to_string w);
              BinOp (MINUS, offset, w)
            end else offset
          | _ -> offset
        end else
          offset)

let increment_stack_ptr (post : Constr.t) (env : Env.t) (offset : Exp.t)
  : Constr.t * Env.t =
  let arch = Env.get_arch env in
  let module Target = (val target_of_arch arch) in
  let sp, _ = Env.get_var env Target.CPU.sp in
  let z3_off, _, _, env = exp_to_z3 offset env in
  Constr.substitute_one post sp z3_off, env

let get_vars (t : Sub.t) : Var.Set.t =
  let visitor =
    (object inherit [Var.Set.t] Term.visitor
      method! visit_def def vars =
        let vars = Var.Set.add vars (Def.lhs def) in
        let vars = Var.Set.union vars (Def.free_vars def) in
        vars
      method! visit_jmp jmp vars =
        Var.Set.union vars (Jmp.free_vars jmp)
    end)
  in
  visitor#visit_sub t Var.Set.empty

(* We are currently filtering out mem from the input variables. We might want
   to add it back, but it causes a great slowdown when Z3 checks the precondition. *)
let get_fun_inputs (sub : Sub.t) (env : Env.t) : Constr.z3_expr list =
  Var.Set.fold (get_vars sub) ~init:[]
    ~f:(fun vars v ->
        match Var.typ v with
        | Imm _ ->
          let z3_v, _ = Env.get_var env v in
          z3_v :: vars
        | _ -> vars)

(* Creates a Z3 function of the form func_ret_outvar(in_vars, ...) which represents
   an output variable to a function call. It is added to the environment, and
   substitutes the original z3_expr representing the output variable. *)
let subst_func_outputs (env : Env.t) (sub : Sub.t) (post : Constr.t)
    ~inputs:(inputs : Constr.z3_expr list) ~outputs:(outputs : Constr.z3_expr list)
  : Constr.t * Env.t =
  let ctx = Env.get_context env in
  let tid = Term.tid sub in
  let input_sorts = List.map inputs ~f:Expr.get_sort in
  let fun_outputs = List.map outputs
      ~f:(fun o ->
          let name = Format.sprintf "%s_ret_%s" (Sub.name sub) (Expr.to_string o) in
          let func_decl = FuncDecl.mk_func_decl_s ctx name input_sorts (Expr.get_sort o) in
          FuncDecl.apply func_decl inputs)
  in
  Constr.substitute post outputs fun_outputs, Env.add_fun_outputs env tid fun_outputs

let spec_verifier_error (sub : Sub.t) (_ : Arch.t) : Env.fun_spec option =
  let name = Sub.name sub in
  if name = "__VERIFIER_error" ||
     name = "__assert_fail" then
    let open Env in
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

let spec_verifier_assume (sub : Sub.t) (arch : Arch.t) : Env.fun_spec option =
  if Sub.name sub = "__VERIFIER_assume" then
    let offset = get_stack_ptr_offset sub arch in
    let open Env in
    Some {
      spec_name = "spec_verifier_assume";
      spec = Summary
          (fun env post tid ->
             let ctx = Env.get_context env in
             let post = set_fun_called post env tid in
             let post, env = increment_stack_ptr post env offset in
             let args = Term.enum arg_t sub in
             let input =
               match Seq.find args
                       ~f:(fun a -> Bap.Std.Arg.intent a = Some Bap.Std.In ||
                                    Bap.Std.Arg.intent a = Some Bap.Std.Both) with
               | Some i -> i
               | None -> failwith "Verifier headerfile must be specified with --api-path" in
             let vars = input |> Bap.Std.Arg.rhs |> Exp.free_vars in
             let v = Var.Set.choose_exn vars in
             let z3_v, env = Env.get_var env v in
             let size = BV.get_size (Expr.get_sort z3_v) in
             let assumption =
               bv_to_bool z3_v ctx size
               |> Constr.mk_goal (Format.sprintf "assume %s" (Expr.to_string z3_v))
               |> Constr.mk_constr
             in
             let post, env = subst_func_outputs env sub post ~inputs:[z3_v] ~outputs:[] in
             Constr.mk_clause [assumption] [post], env)
    }
  else
    None

let spec_verifier_nondet (sub : Sub.t) (arch : Arch.t) : Env.fun_spec option =
  if String.is_prefix (Sub.name sub) ~prefix:"__VERIFIER_nondet_" then
    let offset = get_stack_ptr_offset sub arch in
    let open Env in
    Some {
      spec_name = "spec_verifier_nondet";
      spec = Summary
          (fun env post tid ->
             let post = set_fun_called post env tid in
             let post, env = increment_stack_ptr post env offset in
             let args = Term.enum arg_t sub in
             let output =
               match Seq.find args
                       ~f:(fun a -> Bap.Std.Arg.intent a = Some Bap.Std.Out ||
                                    Bap.Std.Arg.intent a = Some Bap.Std.Both) with
               | Some o -> o
               | None -> failwith "Verifier headerfile must be specified with --api-path" in
             let vars = output |> Bap.Std.Arg.rhs |> Exp.free_vars in
             let v = Var.Set.choose_exn vars in
             let z3_v, env = Env.get_var env v in
             subst_func_outputs env sub post
               ~inputs:(get_fun_inputs sub env) ~outputs:[z3_v])
    }
  else
    None

let spec_arg_terms (sub : Sub.t) (arch : Arch.t) : Env.fun_spec option =
  if Term.first arg_t sub <> None then
    let offset = get_stack_ptr_offset sub arch in
    let open Env in
    Some {
      spec_name = "spec_arg_terms";
      spec = Summary
          (fun env post tid ->
             let post = set_fun_called post env tid in
             let post, env = increment_stack_ptr post env offset in
             let args = Term.enum arg_t sub in
             let outs = Seq.filter args
                 ~f:(fun a -> Bap.Std.Arg.intent a = Some Bap.Std.Out ||
                              Bap.Std.Arg.intent a = Some Bap.Std.Both) in
             (* Build an association list*)
             let chaos = Seq.map outs
                 ~f:(fun a ->
                     let vars = a |> Bap.Std.Arg.rhs |> Exp.free_vars in
                     assert (Var.Set.length vars = 1);
                     let v = Var.Set.choose_exn vars in
                     let z3_v, _ = Env.get_var env v in
                     z3_v)
             in
             let outs = Seq.to_list chaos in
             subst_func_outputs env sub post
               ~inputs:(get_fun_inputs sub env) ~outputs:outs)
    }
  else
    None

let spec_rax_out (sub : Sub.t) (arch : Arch.t) : Env.fun_spec option =
  (* Calling convention for x86 uses EAX as output register. x86_64 uses RAX. *)
  let defs sub =
    Term.enum blk_t sub
    |> Seq.map ~f:(fun b -> Term.enum def_t b)
    |> Seq.concat
  in
  let is_rax def =
    let reg = Var.to_string (Def.lhs def) in
    reg = "RAX" || reg = "EAX"
  in
  if Seq.exists (defs sub) ~f:is_rax then
    (* RAX is a register that is used in the subroutine *)
    let offset = get_stack_ptr_offset sub arch in
    let open Env in
    Some {
      spec_name = "spec_rax_out";
      spec = Summary
          (fun env post tid ->
             let post = set_fun_called post env tid in
             let post, env = increment_stack_ptr post env offset in
             let rax = Seq.find_exn (defs sub) ~f:is_rax |> Def.lhs in
             let z3_v, env = Env.get_var env rax in
             subst_func_outputs env sub post
               ~inputs:(get_fun_inputs sub env) ~outputs:[z3_v])
    }
  else
    None

let spec_default (sub : Sub.t) (arch : Arch.t) : Env.fun_spec =
  let offset = get_stack_ptr_offset sub arch in
  let open Env in
  {
    spec_name = "spec_default";
    spec = Summary (fun env post tid ->
        let post = set_fun_called post env tid in
        let post, env = increment_stack_ptr post env offset in
        subst_func_outputs env sub post
          ~inputs:(get_fun_inputs sub env) ~outputs:[])
  }

let spec_inline (to_inline : Sub.t Seq.t) (sub : Sub.t) (arch : Arch. t): Env.fun_spec =
  let open Env in
  let spec_name = "spec_inline" in
  if Seq.mem to_inline sub ~equal:Sub.equal then
    {
      spec_name = spec_name;
      spec = Inline
    }
  else
    spec_default sub arch

let jmp_spec_default : Env.jmp_spec =
  fun _ _ _ _ -> None

let int_spec_default : Env.int_spec =
  fun env post _ ->
  error "Currently we do not handle system calls%!";
  post, env

let num_unroll : int ref = ref 5

let mk_default_env
    ?jmp_spec:(jmp_spec = jmp_spec_default)
    ?subs:(subs = Seq.empty)
    ?num_loop_unroll:(num_loop_unroll = !num_unroll)
    ?exp_conds:(exp_conds = [])
    ?arch:(arch = `x86_64)
    (ctx : Z3.context)
    (var_gen : Env.var_gen)
  : Env.t =
  let specs = [spec_verifier_error; spec_verifier_assume; spec_verifier_nondet;
               spec_arg_terms; spec_rax_out] in
  Env.mk_env ctx var_gen ~specs ~default_spec:spec_default ~jmp_spec
    ~int_spec:int_spec_default ~subs ~num_loop_unroll ~exp_conds ~arch

let mk_inline_env
    ?num_loop_unroll:(num_loop_unroll = !num_unroll)
    ?exp_conds:(exp_conds = [])
    ?arch:(arch = `x86_64)
    ~subs:(subs : Sub.t Seq.t)
    ~to_inline:(to_inline : Sub.t Seq.t)
    (ctx : Z3.context)
    (var_gen : Env.var_gen)
  : Env.t =
  let specs = [spec_verifier_error; spec_verifier_assume; spec_verifier_nondet] in
  Env.mk_env ctx var_gen ~specs ~default_spec:(spec_inline to_inline)
    ~jmp_spec:jmp_spec_default ~int_spec:int_spec_default ~subs
    ~num_loop_unroll ~exp_conds ~arch

let word_to_z3 (ctx : Z3.context) (w : Word.t) : Constr.z3_expr =
  let fmt = Format.str_formatter in
  Word.pp_dec fmt w;
  let s = Format.flush_str_formatter () in
  BV.mk_numeral ctx s (Word.bitwidth w)

let visit_jmp (env : Env.t) (post : Constr.t) (jmp : Jmp.t) : Constr.t * Env.t =
  let jmp_spec = Env.get_jmp_handler env in
  match jmp_spec env post (Term.tid jmp) jmp with
  | Some p_env -> p_env
  | None ->
    begin
      match Jmp.kind jmp with
      | Goto l ->
        begin
          match l with
          | Direct tid ->
            debug "Goto direct label: %s%!" (Label.to_string l);
            let ctx = Env.get_context env in
            let l_pre =
              match Env.get_precondition env tid with
              | Some pre -> pre
              (* We always hit this point when finish a loop unrolling *)
              | None ->
                error "Precondition for node %s not found!" (Tid.to_string tid);
                failwith ("Error in visit_jmp: \
                           The loop handler should have added the precondition for the node");
            in
            let cond = Jmp.cond jmp in
            let cond_val, assume, vcs, env = exp_to_z3 cond env in
            debug "\n\nJump when %s:\nVCs:%s\nAssumptions:%s\n\n%!"
              (Expr.to_string cond_val) (List.to_string ~f:Constr.to_string vcs)
              (List.to_string ~f:Constr.to_string assume);
            let cond_size = BV.get_size (Expr.get_sort cond_val) in
            let false_cond = Bool.mk_eq ctx cond_val (z3_expr_zero ctx cond_size) in
            let ite = Constr.mk_ite (Term.tid jmp) (Bool.mk_not ctx false_cond) l_pre post in
            let post = ite::vcs in
            Constr.mk_clause assume post, env
          (* TODO: evaluate the indirect jump and
             enumerate the possible concrete values, relate to tids
             (probably tough...) *)
          | Indirect _ ->
            warning "Making an indirect jump, using the default postcondition!\n%!";
            post, env
        end
      | Call call ->
        begin
          let target = Call.target call in
          match Call.return call with
          | Some (Direct tid) ->
            debug "Call label %s with return to %s%!"
              (Label.to_string target) (Tid.to_string tid);
            let ret_pre =
              match Env.get_precondition env tid with
              | Some pre -> pre
              | None ->
                info "Precondition for return %s not found!" (Tid.to_string tid);
                post
            in
            lookup_sub target ret_pre env
          | None ->
            debug "Call label %s with no return%!" (Label.to_string target);
            lookup_sub target post env
          (* If we reach this case, we couldn't figure out the return address *)
          | Some (Indirect _) ->
            warning "Making an indirect call, using the default postcondition!\n%!";
            post, env
        end
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
    end

let visit_elt (env : Env.t) (post : Constr.t) (elt : Blk.elt) : Constr.t * Env.t =
  match elt with
  | `Def def ->
    let var = Def.lhs def in
    let rhs = Def.rhs def in
    let rhs_exp, assume, vcs, env = exp_to_z3 rhs env in
    let z3_var, env = Env.get_var env var in
    let post = post::vcs in
    (* Here we add the assumptions as a hypothesis if there
       are any. *)
    let post = Constr.mk_clause assume post in
    let typ_size t = match t with
      | Bil.Types.Imm n -> n
      | Bil.Types.Mem (_, s) -> Size.in_bits s
      | Bil.Types.Unk ->
        error "Unk type: Unable to obtain type size.%!";
        failwith "visit_elt: elt's type is not representable by Type.t"
    in
    debug "Visiting def:\nlhs = %s : <%d>    rhs = %s : <%d>%!"
      (Expr.to_string z3_var) (var |> Var.typ |> typ_size)
      (Expr.to_string rhs_exp) (rhs |> Type.infer_exn |> typ_size);
    Constr.substitute_one post z3_var rhs_exp, Env.add_var env var z3_var
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

let visit_graph (env : Env.t) (post : Constr.t)
    ~start:start (g : Graphs.Ir.t) : Constr.t * Env.t =
  let module G = Graphlib.Std.Graphlib in
  let leave_node _ n (_, env) =
    let b = Graphs.Ir.Node.label n in
    visit_block env post b in
  (* This function is the identity on forward & cross edges, and
     invokes loop handling code on back edges *)
  let enter_edge kind e ((post, env) as p) : Constr.t * Env.t =
    match kind with
    | `Back ->
      begin
        let src = Graphs.Ir.Edge.src e in
        let dst = Graphs.Ir.Edge.dst e in
        debug "Entering back edge from\n%sto\n%s\n%!"
          (Graphs.Ir.Node.to_string src) (Graphs.Ir.Node.to_string dst);
        let handler = Env.get_loop_handler env in
        post, handler env post ~start:dst g
      end
    | _ -> p
  in
  G.depth_first_search (module Graphs.Ir)
    ~enter_edge:enter_edge ~start:start ~leave_node:leave_node ~init:(post, env)
    g

(* Now that we've defined [visit_graph], we can replace it in the
   [wp_rec_call] placeholder. *)
let _ = Env.wp_rec_call :=
    fun env post ~start g -> visit_graph env post ~start g |> snd

(* BAP currently doesn't have a way to determine that exit does not return.
   This function removes the backedge after the call to exit. *)
let filter (env : Env.t) (calls : string list) (cfg : Graphs.Ir.t) : Graphs.Ir.t =
  let module G = Graphlib.Std.Graphlib in
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
  G.depth_first_search (module Graphs.Ir) ~enter_edge:enter_edge ~init:cfg cfg

let visit_sub (env : Env.t) (post : Constr.t) (sub : Sub.t) : Constr.t * Env.t =
  debug "Visiting sub:\n%s%!" (Sub.to_string sub);
  let cfg = sub |> Sub.to_cfg |> filter env ["exit"] in
  let start = Term.first blk_t sub
              |> Option.value_exn ?here:None ?error:None ?message:None
              |> Graphs.Ir.Node.create in
  let pre, env' = visit_graph ~start:start env post cfg in
  (pre, Env.add_precond env' (Term.tid sub) pre)

(* Replace the [inline_func] placeholder with [visit_sub]. *)
let _  = inline_func :=
    fun post env tid ->
      let subs = Env.get_subs env in
      let target_sub = Seq.find_exn subs ~f:(fun s -> (Term.tid s) = tid) in
      let post = set_fun_called post env tid in
      visit_sub env post target_sub

let collect_non_null_expr (env : Env.t) (exp : Exp.t) : Constr.z3_expr list =
  let ctx = Env.get_context env in
  let visitor =
    begin
      object inherit [Constr.z3_expr list] Exp.visitor
        method! visit_load ~mem:_ ~addr:addr _ _ conds =
          let width = match Type.infer_exn addr with
            | Imm n -> n
            | Mem _ -> error "Expected %s to be an address word!%!" (Exp.to_string addr);
              failwith "Error: in collect_non_null_expr, got a memory read instead of a word"
            | Unk ->
              error "Unk type: Unable to determine if %s is an address word.%!" (Exp.to_string addr);
              failwith "Error: in collect_non_null_expr: addr's type is not representable by Type.t"
          in
          let null = BV.mk_numeral ctx "0" width in
          let addr_val,_,_,_ = exp_to_z3 addr env in
          let non_null_addr = Bool.mk_not ctx (Bool.mk_eq ctx null addr_val) in
          non_null_addr :: conds
      end
    end
  in
  visitor#visit_exp exp []

let jmp_spec_reach (m : bool Tid.Map.t) : Env.jmp_spec =
  let is_goto jmp = match Jmp.kind jmp with Goto _ -> true | _ -> false in
  Tid.Map.fold m ~init:jmp_spec_default
    ~f:(fun ~key ~data spec ->
        fun env post tid jmp ->
          if Tid.(key <> tid) || not (is_goto jmp) then
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
                    let cond_val, assume, vcs, env = exp_to_z3 cond env in
                    debug "\n\nJump when %s:\nVCs:%s\nAssumptions:%s\n\n%!"
                      (Expr.to_string cond_val) (List.to_string ~f:Constr.to_string vcs)
                      (List.to_string ~f:Constr.to_string assume);
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
                    let post = constr @ vcs in
                    Some (Constr.mk_clause assume post, env)
                  | Indirect _ -> None
                end
              | _ -> assert false
            end)

(* This adds a non-null condition for every memory reference in the term *)
let non_null_vc : Env.exp_cond = fun env exp ->
  let ctx = Env.get_context env in
  let conds = collect_non_null_expr env exp in
  if List.is_empty conds then
    None
  else
    Some (Verify (Constr.mk_goal "verify" (Bool.mk_and ctx conds)))

let non_null_assert : Env.exp_cond = fun env exp ->
  let ctx = Env.get_context env in
  let conds = collect_non_null_expr env exp in
  if List.is_empty conds then
    None
  else
    Some (Assume (Constr.mk_goal "assume" (Bool.mk_and ctx conds)))

let mk_smtlib2_post (env : Env.t) (smt_post : string) : Constr.t =
  let ctx = Env.get_context env in
  let sort_symbols = [] in
  let sorts = [] in
  let fun_decls =
    Env.EnvMap.fold (Env.get_var_map env) ~init:[]
      ~f:(fun ~key:_ ~data:z3_var decls ->
          assert (Z3.Expr.is_const z3_var);
          Z3.FuncDecl.mk_const_decl_s ctx
            (Z3.Expr.to_string z3_var)
            (Z3.Expr.get_sort z3_var)
          ::decls
        )
  in
  let fun_symbols =
    Env.EnvMap.fold (Env.get_var_map env) ~init:[]
      ~f:(fun ~key:_ ~data:z3_var decls ->
          assert (Z3.Expr.is_const z3_var);
          Z3.Symbol.mk_string ctx
            (Z3.Expr.to_string z3_var)
          ::decls
        )
  in
  let asts = Z3.SMT.parse_smtlib2_string ctx smt_post
      sort_symbols
      sorts
      fun_symbols
      fun_decls
  in
  let goals = List.map (Z3.AST.ASTVector.to_expr_list asts)
      ~f:(fun e ->
          e
          |> Constr.mk_goal (Expr.to_string e)
          |> Constr.mk_constr)
  in
  Constr.mk_clause [] goals

let check ?refute:(refute = true) (solver : Z3.Solver.solver) (ctx : Z3.context)
    (pre : Constr.t) : Z3.Solver.status =
  info "Evaluating precondition.%!";
  let pre' = Constr.eval pre ctx in
  info "Checking precondition with Z3.\n%!";
  let is_correct =
    if refute then
      Bool.mk_implies ctx pre' (Bool.mk_false ctx)
    else
      pre'
  in
  Z3.Solver.check solver [is_correct]

let print_result (solver : Z3.Solver.solver) (status : Z3.Solver.status)
    (goals: Constr.t) (ctx : Z3.context) : unit =
  match status with
  | Z3.Solver.UNSATISFIABLE -> Format.printf "\nUNSAT!\n%!"
  | Z3.Solver.UNKNOWN -> Format.printf "\nUNKNOWN!\n%!"
  | Z3.Solver.SATISFIABLE ->
    Format.printf "\nSAT!\n%!";
    let model = Z3.Solver.get_model solver
                |> Option.value_exn ?here:None ?error:None ?message:None in
    Format.printf "\nModel:\n%s\n%!" (Z3.Model.to_string model);
    let refuted_goals = Constr.get_refuted_goals goals solver ctx in
    Format.printf "\nRefuted goals:\n%!";
    Seq.iter refuted_goals ~f:(fun g ->
        Format.printf "%s\n%!" (Constr.refuted_goal_to_string g model))

let exclude (solver : Z3.Solver.solver) (ctx : Z3.context) ~var:(var : Constr.z3_expr)
    ~pre:(pre : Constr.t) : Z3.Solver.status =
  let model = Z3.Solver.get_model solver
              |> Option.value_exn ?here:None ?error:None ?message:None in
  let value = Option.value_exn (Z3.Model.eval model var true) in
  let cond = Bool.mk_not ctx (Bool.mk_eq ctx var value) in
  Z3.Solver.push solver;
  Z3.Solver.add solver [cond];
  info "Added constraints: %s\n%!"
    (Z3.Solver.get_assertions solver |> List.to_string ~f:Expr.to_string);
  check solver ctx pre

let get_output_vars (t : Sub.t) (var_names : string list) : Var.Set.t =
  let all_vars = get_vars t in
  let has_name name var = String.equal name (Var.to_string var) in
  List.fold var_names ~init:Var.Set.empty ~f:(fun vars name ->
      match Var.Set.find all_vars ~f:(has_name name) with
      | Some v -> Var.Set.add vars v
      | None ->
        warning "%s not in sub and will not be added to the postcondition" name;
        vars
    )
