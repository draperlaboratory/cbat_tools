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
module Arith = Z3.Arithmetic
module BV = Z3.BitVector
module Bool = Z3.Boolean
module Array = Z3.Z3Array
module Env = Environment

exception Not_implemented of string

let z3_expr_zero (ctx : Z3.context) (size : int) : Env.z3_expr = BV.mk_numeral ctx "0" size
let z3_expr_one (ctx : Z3.context) (size : int) : Env.z3_expr = BV.mk_numeral ctx "1" size

let binop (ctx : Z3.context) (b : binop) : Env.z3_expr -> Env.z3_expr -> Env.z3_expr =
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

let unop (ctx : Z3.context) (u : unop) : Env.z3_expr -> Env.z3_expr =
  let open Bap.Std.Bil.Types in
  match u with
  | NEG -> BV.mk_neg ctx
  | NOT -> BV.mk_not ctx

let cast (ctx : Z3.context) (cst : cast) (i : int) (x : Env.z3_expr) : Env.z3_expr =
  assert (i > 0);
  let size = x |> Expr.get_sort |> BV.get_size in
  let open Bap.Std.Bil.Types in
  match cst with
  | UNSIGNED -> BV.mk_zero_ext ctx (i - size) x
  | SIGNED -> BV.mk_sign_ext ctx (i - size) x
  | HIGH -> BV.mk_extract ctx (size - 1) (size - i) x
  | LOW -> BV.mk_extract ctx (i - 1) 0 x

type args = {
  inputs : Var.Set.t;
  outputs : Var.Set.t;
  both : Var.Set.t;
}

(* Placeholder for inlining function calls, which will be substituted with [visit_sub]
   at its point of definition. *)
let inline_func :
  (Env.z3_expr -> Env.t -> Tid.t -> Env.z3_expr * Env.t) ref =
  ref (fun _ _ _ -> assert false)

let lookup_sub (label : Label.t) (post : Env.z3_expr) (env : Env.t) : Env.z3_expr =
  match label with
  | Direct tid ->
    begin
      match Env.get_sub_handler env tid with
      | Some (Summary compute_func) -> compute_func env post tid
      | Some Inline ->
        let pre, _ = !inline_func post env tid in
        pre
      | None -> post
    end
  (* TODO: Evaluate the expression for the indirect jump and
   * figure out how to handle this case *)
  | Indirect _ -> post

let mk_z3_expr (ctx : Z3.context) ~name:(name : string) ~typ:(typ : Type.t) : Env.z3_expr =
  match typ with
  | Type.Imm size -> BV.mk_const_s ctx name size
  | Type.Mem (i_size, w_size) ->
    debug "Creating memory Mem<%d,%d>%!" (Size.in_bits i_size) (Size.in_bits w_size);
    let i_sort = BV.mk_sort ctx (Size.in_bits i_size) in
    let w_sort = BV.mk_sort ctx (Size.in_bits w_size) in
    Array.mk_const_s ctx name i_sort w_sort

let load_z3_mem (ctx : Z3.context) ~word_size:word_size ~mem:(mem : Env.z3_expr)
    ~addr:(addr : Env.z3_expr) (endian : Bap.Std.endian) : Env.z3_expr =
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
    ~mem:(mem : Env.z3_expr) ~addr:(addr : Env.z3_expr) ~content:(e : Env.z3_expr)
    (endian : Bap.Std.endian) : Env.z3_expr =
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

let new_z3_expr ?name:(name = "fresh_") (env: Env.t) (typ : Type.t) : Env.z3_expr =
  let ctx = Env.get_context env in
  let var_seed = Env.get_var_gen env in
  mk_z3_expr ctx ~name:(Env.get_fresh ~name:name var_seed) ~typ:typ

let var_to_z3 (ctx : Z3.context) (v : Var.t) : Env.z3_expr =
  let full_name = Var.name v ^ (string_of_int (Var.index v)) in
  mk_z3_expr ctx ~name:full_name ~typ:(Var.typ v)

let bv_to_bool (bv : Env.z3_expr) (ctx : Z3.context) (width : int) : Env.z3_expr =
  let zero = z3_expr_zero ctx width in
  Bool.mk_not ctx (Bool.mk_eq ctx bv zero)

let set_fun_called (post : Env.z3_expr) (env : Env.t) (tid : Tid.t) : Env.z3_expr =
  let ctx = Env.get_context env in
  let fun_name = Bool.mk_const_s ctx (Env.get_called env tid |>
                                      Option.value_exn ?here:None ?error:None ?message:None) in
  Z3.Expr.substitute_one post fun_name (Bool.mk_true ctx)

let spec_verifier_error (sub : Sub.t) : Env.fun_spec option =
  let name = Sub.name sub in
  if name = "__VERIFIER_error" ||
     name = "__assert_fail" then
    let open Env in
    Some {
      spec_name = "spec_verifier_error";
      spec = Summary (fun env _ _ -> Bool.mk_false (Env.get_context env))
    }
  else
    None

let spec_verifier_assume (sub : Sub.t) : Env.fun_spec option =
  if Sub.name sub = "__VERIFIER_assume" then
    let open Env in
    Some {
      spec_name = "spec_verifier_assume";
      spec = Summary
          (fun env post tid ->
             let ctx = Env.get_context env in
             let post = set_fun_called post env tid in
             let args = Term.enum arg_t sub in
             let input =
               match Seq.find args
                       ~f:(fun a -> Bap.Std.Arg.intent a = Some Bap.Std.In ||
                                    Bap.Std.Arg.intent a = Some Bap.Std.Both) with
               | Some i -> i
               | None -> failwith "Verifier headerfile must be specified with --api-path" in
             let vars = input |> Bap.Std.Arg.rhs |> Exp.free_vars in
             let v = Var.Set.choose_exn vars in
             let z3_v = Env.get_var env v
                        |> Option.value ~default:(var_to_z3 ctx v) in
             let size = BV.get_size (Expr.get_sort z3_v) in
             Bool.mk_implies ctx (bv_to_bool z3_v ctx size) post)
    }
  else
    None

let spec_verifier_nondet (sub : Sub.t) : Env.fun_spec option =
  if String.is_prefix (Sub.name sub) ~prefix:"__VERIFIER_nondet_" then
    let open Env in
    Some {
      spec_name = "spec_verifier_nondet";
      spec = Summary
          (fun env post tid ->
             let ctx = Env.get_context env in
             let post = set_fun_called post env tid in
             let args = Term.enum arg_t sub in
             let output =
               match Seq.find args
                       ~f:(fun a -> Bap.Std.Arg.intent a = Some Bap.Std.Out ||
                                    Bap.Std.Arg.intent a = Some Bap.Std.Both) with
               | Some o -> o
               | None -> failwith "Verifier headerfile must be specified with --api-path" in
             let vars = output |> Bap.Std.Arg.rhs |> Exp.free_vars in
             let v = Var.Set.choose_exn vars in
             let z3_v = Env.get_var env v
                        |> Option.value ~default:(var_to_z3 ctx v) in
             let fresh = new_z3_expr env ~name:(Sub.name sub ^ "_arg") (Var.typ v) in
             Z3.Expr.substitute_one post z3_v fresh)
    }
  else
    None

let spec_arg_terms (sub : Sub.t) : Env.fun_spec option =
  if Term.first arg_t sub <> None then
    let open Env in
    Some {
      spec_name = "spec_arg_terms";
      spec = Summary
          (fun env post tid ->
             let ctx = Env.get_context env in
             let post = set_fun_called post env tid in
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
                     let z3_v = Env.get_var env v
                                |> Option.value ~default:(var_to_z3 ctx v) in
                     let fresh = new_z3_expr env ~name:(Sub.name sub ^ "_arg") (Var.typ v) in
                     (z3_v, fresh)
                   ) in
             let (subs_from, subs_to) = chaos |> Seq.to_list |> List.unzip in
             Z3.Expr.substitute post subs_from subs_to)
    }
  else
    None

let spec_rax_out (sub : Sub.t) : Env.fun_spec option =
  (* If the architecture is x86_64, the calling convention uses RAX as the output value. *)
  let defs sub =
    Term.enum blk_t sub
    |> Seq.map ~f:(fun b -> Term.enum def_t b)
    |> Seq.concat
  in
  let is_rax def = Var.to_string (Def.lhs def) = "RAX" in
  if Seq.exists (defs sub) ~f:is_rax then
    (* RAX is a register that is used in the subroutine *)
    let open Env in
    Some {
      spec_name = "spec_rax_out";
      spec = Summary
          (fun env post tid ->
             let ctx = Env.get_context env in
             let post = set_fun_called post env tid in
             let rax = Seq.find_exn (defs sub) ~f:is_rax |> Def.lhs in
             let z3_v = Env.get_var env rax
                        |> Option.value ~default:(var_to_z3 ctx rax) in
             let fresh = new_z3_expr env ~name:(Sub.name sub ^ "_arg") (Var.typ rax) in
             Z3.Expr.substitute_one post z3_v fresh)
    }
  else
    None

let spec_default : Env.fun_spec =
  let open Env in
  {
    spec_name = "spec_default";
    spec = Summary (fun post env tid -> set_fun_called env post tid)
  }

let spec_inline : Env.fun_spec =
  let open Env in
  {
    spec_name = "spec_inline";
    spec = Inline
  }

let jmp_spec_default : Env.jmp_spec =
  fun _ _ _ _ -> None

let int_spec_default : Env.int_spec =
  fun _ post _ ->
  error "Currently we do not handle system calls%!";
  post

let num_unroll : int ref = ref 5

let mk_default_env
    ?jmp_spec:(jmp_spec = jmp_spec_default)
    ?subs:(subs = Seq.empty)
    ?num_loop_unroll:(num_loop_unroll = !num_unroll)
    ?exp_conds:(exp_conds = [])
    (ctx : Z3.context)
    (var_gen : Env.var_gen)
  : Env.t =
  let specs = [spec_verifier_error; spec_verifier_assume; spec_verifier_nondet;
               spec_arg_terms; spec_rax_out] in
  Env.mk_env ctx var_gen ~specs ~default_spec:spec_default ~jmp_spec
    ~int_spec:int_spec_default ~subs ~num_loop_unroll ~exp_conds

let mk_inline_env
    ?num_loop_unroll:(num_loop_unroll = !num_unroll)
    ?exp_conds:(exp_conds = [])
    ~subs:(subs : Sub.t Seq.t)
    (ctx : Z3.context)
    (var_gen : Env.var_gen)
  : Env.t =
  let specs = [spec_verifier_error; spec_verifier_assume; spec_verifier_nondet] in
  Env.mk_env ctx var_gen ~specs ~default_spec:spec_inline
    ~jmp_spec:jmp_spec_default ~int_spec:int_spec_default ~subs
    ~num_loop_unroll ~exp_conds

let sub_args (sub : Sub.t) : args =
  let new_args = { inputs = Var.Set.empty; outputs = Var.Set.empty; both = Var.Set.empty } in
  if spec_arg_terms sub <> None then
    (* The subroutine has arg_t terms that we can iterate over to find the input/output args *)
    Seq.fold (Term.enum arg_t sub) ~init:new_args
      ~f:(fun args a ->
          match Bap.Std.Arg.intent a, Exp.free_vars (Bap.Std.Arg.rhs a) with
          | Some In, v -> { args with inputs = Var.Set.union args.inputs v }
          | Some Out, v -> { args with outputs = Var.Set.union args.outputs v }
          | Some Both, v -> { args with both = Var.Set.union args.both v }
          | None, _ -> args)
  else if spec_rax_out sub <> None then
    (* The subroutine uses RAX as an output register if RAX is defined on the LHS in the sub *)
    let defs = Term.enum blk_t sub |> Seq.map ~f:(fun b -> Term.enum def_t b) |> Seq.concat in
    match Seq.find defs ~f:(fun d -> Var.to_string (Def.lhs d) = "RAX") with
    | Some r -> { new_args with outputs = Var.Set.union new_args.outputs (Var.Set.singleton @@ Def.lhs r) }
    | None -> new_args
  else
    begin
      (* Default case: We are generating a trivial sub compare in this case *)
      warning "Input and output variables for %s are empty%!" (Sub.name sub);
      new_args
    end

let get_output_vars (sub : Sub.t) : Var.Set.t =
  let args = sub_args sub in
  Var.Set.union args.outputs args.both

let word_to_z3 (ctx : Z3.context) (w : Word.t) : Env.z3_expr =
  let fmt = Format.str_formatter in
  Word.pp_dec fmt w;
  let s = Format.flush_str_formatter () in
  BV.mk_numeral ctx s (Word.bitwidth w)

let exp_to_z3 (exp : Exp.t) (env : Env.t) : Env.z3_expr * Env.z3_expr list * Env.z3_expr list =
  let ctx = Env.get_context env in
  let read_from_env env v =
    match Env.get_var env v with
    | Some w -> w
    | None -> var_to_z3 ctx v
  in
  let open Bap.Std.Bil.Types in
  let rec exp_to_z3_body exp env =
    match exp with
    | Load (mem, addr, endian, size) ->
      debug "Visiting load: Mem:%s  Addr:%s  Size:%s%!"
        (Exp.to_string mem) (Exp.to_string addr) (Size.to_string size);
      let mem_val = exp_to_z3_body mem env in
      let addr_val = exp_to_z3_body addr env in
      load_z3_mem ctx ~word_size:(Size.in_bits size) ~mem:mem_val ~addr:addr_val endian
    | Store (mem, addr, exp, endian, size) ->
      debug "Visiting store: Mem:%s  Addr:%s  Exp:%s  Size:%s%!"
        (Exp.to_string mem) (Exp.to_string addr) (Exp.to_string exp) (Size.to_string size);
      let mem_val = exp_to_z3_body mem env in
      let addr_val = exp_to_z3_body addr env in
      let exp_val = exp_to_z3_body exp env in
      store_z3_mem ctx ~word_size:(Size.in_bits size)
        ~mem:mem_val ~addr:addr_val ~content:exp_val endian
    | BinOp (bop, x, y) ->
      debug "Visiting binop: %s %s %s%!"
        (Exp.to_string x) (Bil.string_of_binop bop) (Exp.to_string y);
      let x_val = exp_to_z3_body x env in
      let y_val = exp_to_z3_body y env in
      let x_size = x_val |> Expr.get_sort |> BV.get_size in
      let y_size = y_val |> Expr.get_sort |> BV.get_size in
      assert (x_size = y_size);
      binop ctx bop x_val y_val
    | UnOp (u, x) ->
      debug "Visiting unop: %s %s%!" (Bil.string_of_unop u) (Exp.to_string x);
      let x_val = exp_to_z3_body x env in
      unop ctx u x_val
    | Var v ->
      debug "Visiting var: %s%!" (Var.to_string v);
      read_from_env env v
    | Bil.Types.Int w ->
      debug "Visiting int: %s%!" (Word.to_string w);
      let fmt = Format.str_formatter in
      Word.pp_dec fmt w;
      let s = Format.flush_str_formatter () in
      BV.mk_numeral ctx s (Word.bitwidth w)
    | Cast (cst, i, x) ->
      debug "Visiting cast: %s from %d to %s%!"
        (Bil.string_of_cast cst) i (Exp.to_string x);
      let x_val = exp_to_z3_body x env in
      cast ctx cst i x_val
    | Let (v, exp, body) ->
      debug "Visiting let %s = %s in %s%!"
        (Var.to_string v) (Exp.to_string exp) (Exp.to_string body);
      let exp_val = exp_to_z3_body exp env in
      let env' = Env.add_var env v exp_val in
      exp_to_z3_body body env'
    | Unknown (str, typ) ->
      debug "Visiting unknown: %s  Type:%s%!" str (Type.to_string typ);
      new_z3_expr env ~name:("unknown_" ^ str) typ
    | Ite (cond, yes, no) ->
      debug "Visiting ite: if %s\nthen %s\nelse %s%!"
        (Exp.to_string cond) (Exp.to_string yes) (Exp.to_string no);
      let cond_val = exp_to_z3_body cond env in
      let cond_size = BV.get_size (Expr.get_sort cond_val) in
      let yes_val = exp_to_z3_body yes env in
      let no_val = exp_to_z3_body no env in
      Bool.mk_ite ctx (bv_to_bool cond_val ctx cond_size) yes_val no_val
    | Extract (high, low, exp) ->
      debug "Visiting extract: High:%d Low:%d Exp:%s%!" high low (Exp.to_string exp);
      let exp_val = exp_to_z3_body exp env in
      BV.mk_extract ctx high low exp_val
    | Concat (w1, w2) ->
      debug "Visiting concat: %s ^ %s%!" (Exp.to_string w1) (Exp.to_string w2);
      let w1_val = exp_to_z3_body w1 env in
      let w2_val = exp_to_z3_body w2 env in
      BV.mk_concat ctx w1_val w2_val
  in
  let assume, verify = Env.mk_exp_conds env exp in
  exp_to_z3_body exp env, assume, verify

let visit_jmp (env : Env.t) (post : Env.z3_expr) (jmp : Jmp.t) : Env.z3_expr =
  let jmp_spec = Env.get_jmp_handler env in
  match jmp_spec env post (Term.tid jmp) jmp with
  | Some pre -> pre
  | None ->
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
            let cond_val, assume, vcs = exp_to_z3 cond env in
            debug "\n\nJump when %s:\nVCs:%s\nAssumptions:%s\n\n%!"
              (Expr.to_string cond_val) (List.to_string ~f:Expr.to_string vcs)
              (List.to_string ~f:Expr.to_string assume);
            let cond_size = BV.get_size (Expr.get_sort cond_val) in
            let false_cond = Bool.mk_eq ctx cond_val (z3_expr_zero ctx cond_size) in
            let ite = Bool.mk_ite ctx (Bool.mk_not ctx false_cond) l_pre post in
            let post = Bool.mk_and ctx (ite::vcs) in
            if List.is_empty assume then post else
              Bool.mk_implies ctx (Bool.mk_and ctx assume) post
          (* TODO: evaluate the indirect jump and
             enumerate the possible concrete values, relate to tids
             (probably tough...) *)
          | Indirect _ ->
            warning "Making an indirect jump, using the default postcondition!\n%!";
            post
        end
      | Call call ->
        begin
          let target = Call.target call in
          match Call.return call with
          | Some (Direct tid) ->
            debug "Call label %s with return to %s%!"
              (Label.to_string target) (Tid.to_string tid);
            let ret_pre = Env.get_precondition env tid |>
                          Option.value_exn ?here:None ?error:None ?message:None in
            lookup_sub target ret_pre env
          | None ->
            debug "Call label %s with no return%!" (Label.to_string target);
            lookup_sub target post env
          (* If we reach this case, we couldn't figure out the return address *)
          | Some (Indirect _) ->
            warning "Making an indirect call, using the default postcondition!\n%!";
            post
        end
      (* TODO: do something here? *)
      | Ret l ->
        debug "Return to: %s%!" (Label.to_string l);
        post
      (* FIXME: do something here *)
      | Int (i, tid) ->
        debug "Interrupt %d with return to %s%!" i (Tid.to_string tid);
        let ret_pre = Env.get_precondition env tid |>
                      Option.value_exn ?here:None ?error:None ?message:None in
        let handler = Env.get_int_handler env in
        handler env ret_pre i
    end

let visit_elt (env : Env.t) (post : Env.z3_expr) (elt : Blk.elt) : Env.z3_expr * Env.t =
  match elt with
  | `Def def ->
    let ctx = Env.get_context env in
    let var = Def.lhs def in
    let rhs = Def.rhs def in
    let z3_var = var_to_z3 ctx var in
    let rhs_exp, assume, vcs = exp_to_z3 rhs env in
    let post = Bool.mk_and ctx (post::vcs) in
    (* Here we add the assumptions as a hypothesis if there
       are any. *)
    let post = if List.is_empty assume then post else
        Bool.mk_implies ctx (Bool.mk_and ctx assume) post
    in
    let typ_size t = match t with
      | Bil.Types.Imm n -> n
      | Bil.Types.Mem (_, s) -> Size.in_bits s in
    debug "Visiting def:\nlhs = %s : <%d>    rhs = %s : <%d>%!"
      (Expr.to_string z3_var) (var |> Var.typ |> typ_size)
      (Expr.to_string rhs_exp) (rhs |> Type.infer_exn |> typ_size);
    Expr.substitute_one post z3_var rhs_exp, Env.add_var env var z3_var
  | `Jmp jmp ->
    visit_jmp env post jmp, env
  | `Phi _ ->
    error "We do not currently handle Phi nodes.\n%!";
    raise (Not_implemented "visit_elt: case `Phi(phi) not implemented")

let visit_block (env : Env.t) (post : Env.z3_expr) (blk : Blk.t) : Env.z3_expr * Env.t =
  debug "Visiting block:\n%s%!" (Blk.to_string blk);
  let compute_pre b =
    Seq.fold b ~init:(post, env) ~f:(fun (pre, env) a -> visit_elt env pre a)
  in
  let pre, env = blk |> Blk.elts ~rev:true |> compute_pre in
  (pre, Env.add_precond env (Term.tid blk) pre)

let visit_graph (env : Env.t) (post : Env.z3_expr)
    ~start:start (g : Graphs.Ir.t) : Env.z3_expr * Env.t =
  let module G = Graphlib.Std.Graphlib in
  let leave_node _ n (_, env) =
    let b = Graphs.Ir.Node.label n in
    visit_block env post b in
  (* This function is the identity on forward & cross edges, and
     invokes loop handling code on back edges *)
  let enter_edge kind e ((post, env) as p) : Env.z3_expr * Env.t =
    match kind with
    | `Back ->
      begin
        info "Entering back edge\n%!";
        let tgt_node = e |> Graphs.Ir.Edge.dst in
        let handler = Env.get_loop_handler env in
        post, handler env post ~start:tgt_node g
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

let visit_sub (env : Env.t) (post : Env.z3_expr) (sub : Sub.t) : Env.z3_expr * Env.t =
  debug "Visiting sub:\n%s%!" (Sub.to_string sub);
  let cfg = Sub.to_cfg sub in
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

let collect_non_null_expr (env : Env.t) (exp : Exp.t) : Env.z3_expr list =
  let ctx = Env.get_context env in
  let visitor =
    begin
      object inherit [Env.z3_expr list] Exp.visitor
        method! visit_load ~mem:_ ~addr:addr _ _ conds =
          let width = match Type.infer_exn addr with
            | Imm n -> n
            | Mem _ -> error "Expected %s to be an address word!%!" (Exp.to_string addr);
              failwith "Error: in collect_non_null_expr, got a memory read instead of a word"
          in
          let null = BV.mk_numeral ctx "0" width in
          let addr_val,_,_ = exp_to_z3 addr env in
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
                    let cond_val, assume, vcs = exp_to_z3 cond env in
                    debug "\n\nJump when %s:\nVCs:%s\nAssumptions:%s\n\n%!"
                      (Expr.to_string cond_val) (List.to_string ~f:Expr.to_string vcs)
                      (List.to_string ~f:Expr.to_string assume);
                    let cond_size = BV.get_size (Expr.get_sort cond_val) in
                    let false_cond = Bool.mk_eq ctx cond_val (z3_expr_zero ctx cond_size) in
                    (* let ite = Bool.mk_ite ctx (Bool.mk_not ctx false_cond) l_pre post in *)
                    let constr = if data then
                        [Bool.mk_not ctx false_cond; l_pre]
                      else
                        [false_cond; post]
                    in    
                    let post = Bool.mk_and ctx (constr @ vcs) in
                    if List.is_empty assume then Some post else
                      Some (Bool.mk_implies ctx (Bool.mk_and ctx assume) post)
                  | Indirect _ ->
                    warning "Making an indirect jump, using the default postcondition!\n%!";
                    Some post
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
    Some (Verify (Bool.mk_and ctx conds))

let non_null_assert : Env.exp_cond = fun env exp ->
  let ctx = Env.get_context env in
  let conds = collect_non_null_expr env exp in
  if List.is_empty conds then
    None
  else
    Some (Assume (Bool.mk_and ctx conds))

let mk_smtlib2_post (env : Env.t) (smt_post : string) : Env.z3_expr =
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
  asts |> Z3.AST.ASTVector.to_expr_list |> Bool.mk_and ctx

let check (solver : Z3.Solver.solver) (ctx : Z3.context) (pre : Env.z3_expr)
  : Z3.Solver.status =
  let is_correct = Bool.mk_implies ctx pre (Bool.mk_false ctx) in
  Z3.Solver.check solver [is_correct]

let print_result (solver : Z3.Solver.solver) (status : Z3.Solver.status) : unit =
  match status with
  | Z3.Solver.UNSATISFIABLE -> Printf.printf "\nUNSAT!\n%!"
  | Z3.Solver.UNKNOWN -> Printf.printf "\nUNKNOWN!\n%!"
  | Z3.Solver.SATISFIABLE ->
    let model = Z3.Solver.get_model solver
                |> Option.value_exn ?here:None ?error:None ?message:None in
    Printf.printf "\nSAT!\n%!";
    Printf.printf "Model:\n%s\n%!" (Z3.Model.to_string model)

let exclude (solver : Z3.Solver.solver) (ctx : Z3.context) ~var:(var : Env.z3_expr)
    ~pre:(pre : Env.z3_expr) : Z3.Solver.status =
  let model = Z3.Solver.get_model solver
              |> Option.value_exn ?here:None ?error:None ?message:None in
  let value = Option.value_exn (Z3.Model.eval model var true) in
  let cond = Bool.mk_not ctx (Bool.mk_eq ctx var value) in
  Z3.Solver.push solver;
  Z3.Solver.add solver [cond];
  info "Added constraints: %s\n%!"
    (Z3.Solver.get_assertions solver |> List.to_string ~f:Expr.to_string);
  check solver ctx pre

let get_vars (t : sub term) : Var.Set.t =
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
