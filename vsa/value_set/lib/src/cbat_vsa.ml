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

include Core_kernel
open Bap.Std
open Graphlib.Std
open Cbat_vsa_utils

module CG = Graphs.Callgraph
module CFG = Graphs.Tid

module AI = Cbat_ai_representation
module WordSet = Cbat_clp_set_composite
module Mem = Cbat_ai_memmap
module Word_ops = Cbat_word_ops
module Utils = Cbat_vsa_utils
module Back_edges = Cbat_back_edges

(* Set up BAP to tag blocks with their preconditions *)
let precond = Value.Tag.register (module AI)
    ~name:"vsa precondition"
    ~uuid:"650594fc-0c9d-46d1-b391-8193357b537d"

(* a tag used in the analysis to indicate when to
   widen a precondition state *)
let do_widen = Value.Tag.register (module Unit)
    ~name:"widen state on recompute"
    ~uuid:"a8050d49-f451-4684-afbd-97c013dd8e4d"

let clear_do_widen (s : sub term) : sub term =
  Term.map blk_t s ~f:begin fun blk ->
    Term.del_attr blk do_widen
  end

let jmp_target (j : jmp term) : tid option =
  let mlbl = match Jmp.kind j with
    | Call c -> Some (Call.target c)
    | Goto lbl
    | Ret lbl -> Some lbl
    | Int _ -> None in
  Option.bind mlbl ~f:begin fun lbl ->
    match lbl with
    | Direct tid -> Some tid
    | Indirect _ -> None
  end

let label_widening_points (sub : sub term) : sub term =
  let open Monads.Std.Monad.Option.Syntax in
  Term.enum blk_t sub
  |> Seq.concat_map ~f:(Term.enum jmp_t)
  |> Seq.fold ~init:sub ~f:begin fun sub jmp ->
    if Term.has_attr jmp Back_edges.back_edge then
      Option.value ~default:sub begin
        Term.get_attr jmp Back_edges.back_edge >>= fun () ->
        jmp_target jmp >>= fun tid ->
        let set_do_widen blk = Term.set_attr blk do_widen () in
        !!(Term.change blk_t sub tid (Option.map ~f:set_do_widen))
      end
    else sub
  end

type wordset = WordSet.t


(* Denotations
   =========================================================
   These functions are denotations of terms in BIR
 *)


(* bitwidth is the width of the two inputs *)
let denote_binop (op : Bil.binop) : wordset -> wordset -> wordset =
  let btrue = WordSet.singleton Word.b1 in
  let bfalse = WordSet.singleton Word.b0 in
  let wordset_of_bool b = if b then btrue else bfalse in
  let bool_top = WordSet.top 1 in
  let bool_bottom = WordSet.bottom 1 in
  match op with
  | Bil.PLUS -> WordSet.add
  | Bil.MINUS -> WordSet.sub
  | Bil.TIMES -> WordSet.mul
  | Bil.LSHIFT -> WordSet.lshift
  | Bil.RSHIFT -> WordSet.rshift
  | Bil.ARSHIFT -> WordSet.arshift
  | Bil.DIVIDE -> WordSet.div
  | Bil.SDIVIDE -> WordSet.sdiv
  | Bil.MOD -> WordSet.modulo
  | Bil.SMOD -> WordSet.smodulo
  | Bil.AND -> WordSet.logand
  | Bil.OR -> WordSet.logor
  | Bil.XOR -> WordSet.logxor
  | Bil.EQ -> fun v1 v2 ->
    let v1Size = WordSet.cardinality v1 in
    let v2Size = WordSet.cardinality v2 in
    (* If either expression doesn't have a value, then neither
       does the result of the comparison.
    *)
    if Word.is_zero v1Size || Word.is_zero v2Size then bool_bottom
    (* If both expressions have values and one of them has multiple
       possible values, then either they overlap at one or more values or not.
       If they do, the comparison may return true or false, if not, the
       comparison must return false.
    *)
    else if Word_ops.is_one v1Size && Word_ops.is_one v2Size
    then wordset_of_bool @@ WordSet.equal v1 v2
    else if WordSet.overlap v1 v2 then bool_top else bfalse
  | Bil.NEQ -> fun v1 v2 ->
    let v1Size = WordSet.cardinality v1 in
    let v2Size = WordSet.cardinality v2 in
    if Word.is_zero v1Size || Word.is_zero v2Size then bool_bottom
    else if Word_ops.is_one v1Size && Word_ops.is_one v2Size
    then wordset_of_bool @@ not @@ WordSet.equal v1 v2
    else if WordSet.overlap v1 v2 then bool_top else btrue
  | Bil.LT -> fun v1 v2 ->
    let open Monads.Std.Monad.Option in
    Option.value ~default:bool_bottom
      begin
        WordSet.max_elem v1 >>= fun v1_max ->
        WordSet.min_elem v1 >>= fun v1_min ->
        WordSet.max_elem v2 >>= fun v2_max ->
        WordSet.min_elem v2 >>= fun v2_min ->
        (* If all elements of v1 are less than all elements of
           v2, then the comparison is always true. If they are
           all greater than or equal to all elements in v2, then
           the comparison is always false. Otherwise, the
           comparison may be true or false.
        *)
        if Word.(<) v1_max v2_min then return btrue
        else if Word.(>=) v1_min v2_max then return bfalse
        else return bool_top
      end
  | Bil.LE -> fun v1 v2 ->
    let open Monads.Std.Monad.Option in
    Option.value ~default:bool_bottom
      begin
        WordSet.max_elem v1 >>= fun v1_max ->
        WordSet.min_elem v1 >>= fun v1_min ->
        WordSet.max_elem v2 >>= fun v2_max ->
        WordSet.min_elem v2 >>= fun v2_min ->
        if Word.(<=) v1_max v2_min then return btrue
        else if Word.(>) v1_min v2_max then return bfalse
        else return bool_top
      end
  | Bil.SLT -> fun v1 v2 ->
    let open Monads.Std.Monad.Option in
    Option.value ~default:bool_bottom
      begin
        WordSet.max_elem_signed v1 >>= fun v1_max ->
        WordSet.min_elem_signed v1 >>= fun v1_min ->
        WordSet.max_elem_signed v2 >>= fun v2_max ->
        WordSet.min_elem_signed v2 >>= fun v2_min ->
        (* If all elements of v1 are less than all elements of
           v2, then the comparison is always true. If they are
           all greater than or equal to all elements in v2, then
           the comparison is always false. Otherwise, the
           comparison may be true or false.
        *)
        if Word.(<) (Word.signed v1_max) (Word.signed v2_min) then return btrue
        else if Word.(>=) (Word.signed v1_min) (Word.signed v2_max) then return bfalse
        else return bool_top
      end
  | Bil.SLE -> fun v1 v2 ->
    let open Monads.Std.Monad.Option in
    Option.value ~default:bool_bottom
      begin
        WordSet.max_elem_signed v1 >>= fun v1_max ->
        WordSet.min_elem_signed v1 >>= fun v1_min ->
        WordSet.max_elem_signed v2 >>= fun v2_max ->
        WordSet.min_elem_signed v2 >>= fun v2_min ->
        if Word.(<=) (Word.signed v1_max) (Word.signed v2_min) then return btrue
        else if Word.(>) (Word.signed v1_min) (Word.signed v2_max) then return bfalse
        else return bool_top
      end

type val_t = [`Mem of Mem.t | `Word of wordset]

module Monad_type_error = Monads.Std.Monad.Result.Make(Type.Error)(Monads.Std.Monad.Ident)
type 'a or_type_error = ('a, Type.error) Result.t

let val_as_mem (v : val_t) : Mem.t or_type_error =
  match v with
  | `Mem m -> Ok m
  | `Word _ -> Error Type.Error.bad_mem

let val_as_imm (v : val_t) : wordset or_type_error =
  match v with
  | `Word p -> Ok p
  | `Mem _ -> Error Type.Error.bad_imm

let val_join (v1 : val_t) (v2 : val_t) : val_t or_type_error =
  let open Monad_type_error in
  match v1 with
  | `Word p1 -> val_as_imm v2 >>= fun p2 -> return @@ `Word (WordSet.join p1 p2)
  | `Mem m1 -> val_as_mem v2 >>= fun m2 -> return @@ `Mem (Mem.join m1 m2)

let val_top : typ -> val_t = function
  | Type.Imm i -> `Word (WordSet.top i)
  | Type.Mem (addr_sz, addressable_sz) ->
    let addr_width = Size.in_bits addr_sz in
    let addressable_width = Size.in_bits addressable_sz in
    let k = {Mem.addr_width = addr_width;
             Mem.addressable_width = addressable_width} in
    `Mem (Mem.top k)
  | Type.Unk -> failwith "Error in val_top: typ is not representable by Type.t"

let val_bottom : typ -> val_t = function
  | Type.Imm i -> `Word (WordSet.bottom i)
  | Type.Mem (addr_sz, addressable_sz) ->
    let addr_width = Size.in_bits addr_sz in
    (* TODO: addressable_width an overgeneralization; simplify *)
    let addressable_width = Size.in_bits addressable_sz in
    let k = {Mem.addr_width = addr_width;
             Mem.addressable_width = addressable_width} in
    `Mem (Mem.bottom k)
  | Type.Unk -> failwith "Error in val_bottom: typ is not representable by Type.t"

(* Helper functions; define a denotation for expressions.
   Assumes that e has BIR type [Imm bitwidth]
*)
let rec denote_exp (e : exp) (env : AI.t) : val_t or_type_error =
  let open Monad_type_error in
  let monadic_assert (b : bool) (err : Type.error) =
    if b then !!() else fail err in
  let return_imm (v : wordset) = return @@ `Word v in
  let return_mem (v : Mem.t) = return @@ `Mem v in
  match e with
  | Bil.Var v -> begin match Var.typ v with
    | Type.Imm bitwidth -> return_imm @@ AI.find_word bitwidth env v
    | Type.Mem (addr_i, addressable_size) ->
      let addr_width : int = Size.in_bits addr_i in
      let addressable_width : int = Size.in_bits addressable_size in
      let k = {Mem.addr_width = addr_width;
               Mem.addressable_width = addressable_width} in
      return_mem @@ AI.find_memory k env v
    | Type.Unk -> failwith "Error in denote_exp: var type is not representable by Type.t"
    end
  | Bil.Int bv -> return_imm @@ WordSet.singleton bv
  | Bil.BinOp (op, e1, e2) ->
    denote_exp e1 env >>= val_as_imm >>= fun v1 ->
    denote_exp e2 env >>= val_as_imm >>= fun v2 ->
    return_imm @@ denote_binop op v1 v2
  | Bil.Load (m, a, e, s) ->
    denote_exp a env >>= val_as_imm >>= fun addr ->
    denote_exp m env >>= val_as_mem >>= fun mv ->
    let resSize = Size.in_bits s in
    if WordSet.splits_by addr (Word.of_int ~width:resSize (Size.in_bytes s))
    then Option.value_map ~default:(return_imm @@ WordSet.bottom resSize) (Mem.Key.of_wordset addr)
        ~f:(fun k -> Mem.find (resSize, e) mv k |> Mem.Val.data |> return_imm)
    else return_imm @@ WordSet.top resSize
  | Bil.Store (m, a, u, e, s) ->
    Type.infer u >>= fun u_typ ->
    let sz = Size.in_bits s in
    let exp = Type.imm sz in
    let u_type_error = Type.Error.bad_type ~exp ~got:u_typ in
    monadic_assert Type.(exp = u_typ) u_type_error >>= fun () ->
    denote_exp a env >>= val_as_imm >>= fun addr ->
    denote_exp m env >>= val_as_mem >>= fun mv ->
    denote_exp u env >>= val_as_imm >>= fun v ->
    (* Check that the store can be represented by a repeating sequence of vs *)
    let v' = if WordSet.splits_by addr (Word.of_int ~width:sz (Size.in_bytes s))
      then v else WordSet.top sz in
    let data = Mem.Val.create v' e in
    return_mem @@ Option.value_map ~default:mv (Mem.Key.of_wordset addr)
      ~f:(fun key -> Mem.add mv ~key ~data)
  | Bil.Ite (cond, yes, no) ->
    denote_exp cond env >>= val_as_imm >>= fun condv ->
    denote_exp yes env >>= fun yesv ->
    denote_exp no env >>= fun nov ->
    Type.infer yes >>= fun yes_ty ->
    let bottom = val_bottom yes_ty in
    if WordSet.is_top condv then val_join yesv nov
    else if WordSet.equal condv (WordSet.singleton Word.b1) then return yesv
    else if WordSet.equal condv (WordSet.singleton Word.b0) then return nov
    else return bottom
  | Bil.Extract (hi, lo, e) ->
    denote_exp e env >>= val_as_imm >>= fun v ->
    return_imm @@ WordSet.extract ~hi ~lo v
  | Bil.Concat (e1, e2) ->
    denote_exp e1 env >>= val_as_imm >>= fun v1 ->
    denote_exp e2 env >>= val_as_imm >>= fun v2 ->
    return_imm @@ WordSet.concat v1 v2
  | Bil.UnOp (Bil.NOT, e) ->
    denote_exp e env >>= val_as_imm >>| WordSet.lnot >>= return_imm
  | Bil.UnOp (Bil.NEG, e) ->
    denote_exp e env >>= val_as_imm >>| WordSet.neg >>= return_imm
  | Bil.Cast (ct, sz, e) ->
    denote_exp e env >>= val_as_imm >>| WordSet.cast ct sz >>= return_imm
  | Bil.Let (var, value, body) ->
    denote_exp value env >>= fun v ->
    let env' = match v with
      | `Word p -> AI.add_word ~key:var ~data:p env
      | `Mem m -> AI.add_memory ~key:var ~data:m env
    in
    denote_exp body env'
  | Bil.Unknown (_,typ) -> return @@ val_top typ

let denote_imm_exp (e : exp) (env : AI.t) : WordSet.t or_type_error =
  let open Monad_type_error in
  denote_exp e env >>= val_as_imm

let denote_mem_exp (e : exp) (env : AI.t) : Mem.t or_type_error =
  let open Monad_type_error in
  denote_exp e env >>= val_as_mem

let denote_def df env : AI.t =
  let v = Def.lhs df in
  let e = Def.rhs df in
  exn_on_err @@
  let open Monad_type_error in
  (* TODO: throw errors here or later? *)
  denote_exp e env >>| fun ev ->
  match ev with
  | `Word p -> AI.add_word env ~key:v ~data:p
  | `Mem m -> AI.add_memory env ~key:v ~data:m

(* Computes the denotation of a block's def statements, i.e.
   the effect they have on the precondition abstraction.
*)
let denote_defs (b : blk term) : AI.t -> AI.t =
  let identity x = x in
  let compose_denote (d : AI.t -> AI.t) df (env : AI.t) = denote_def df (d env) in
  let phi_res = Seq.fold (Term.enum phi_t b) ~init:identity
      ~f:(fun _ -> not_implemented "denotation of phi node") in
  Seq.fold (Term.enum def_t b) ~f:compose_denote ~init:phi_res



(* Filters a sequence of jumps by which are reachable in the given environment *)
(* TODO: use jump condition processing to make this more accurate *)
let reachable_jumps (env : AI.t) (jmps : jmp term seq) : jmp term seq =
  Seq.unfold_with jmps  ~init:true ~f:begin fun reachable jmp ->
    let cond = exn_on_err @@ denote_imm_exp (Jmp.cond jmp) env in
    let can_fall_through = WordSet.elem Word.b0 cond in
    if not reachable then Seq.Step.Done
    else if WordSet.elem Word.b1 cond then Seq.Step.Yield (jmp, can_fall_through)
    else Seq.Step.Skip can_fall_through
  end


(* Computes the denotation of the jumps of a basic block.
   Inputs are a denotation function for subroutine calls,
   the block whose jumps to denote, the block postcondition
   environment invariants that hold before the jumps, and
   the target to be jumped to.
   TODO: make inferences from the value of the flag when
   a jump is taken
*)
let denote_jump (denote_call : sub:tid -> AI.t -> target:tid -> AI.t)
    (b : blk term)  (env : AI.t) ~(target : tid) : AI.t =
  Term.enum jmp_t b
  |> reachable_jumps env
  |> Seq.map ~f:begin fun jmp ->
    let inspect_call c =
      Format.printf "//Assuming a well-formed call-return control flow@.";
      match Call.return c with
        | None -> AI.bottom
        | Some (Direct tid) when compare_tid target tid <> 0 -> AI.bottom
        | Some (Indirect _)
        | Some (Direct _) ->
          (* In this case, the call might return to target *)
          begin match Call.target c with
            | Indirect _ -> AI.top
            | Direct sub -> denote_call ~sub env ~target
          end in
    begin match Jmp.kind jmp with
      | Int _ -> not_implemented ~top:AI.top "interrupt denotation"
      | Call c -> inspect_call c
      | Goto (Direct tid)
      | Ret (Direct tid) ->  if compare_tid target tid = 0 then env else AI.bottom
      | Goto (Indirect _)
      | Ret (Indirect _) -> env
      end
  end
  |> Seq.fold ~init:AI.bottom ~f:AI.join

(* Computes the denotation of a block in a context-sensitive way,
   dependent on which block is next reached.
*)
let denote_block (denote_call : sub:tid -> AI.t -> target:tid -> AI.t)
    (ctx : program term) ~(source : tid) (env : AI.t) : target:tid -> AI.t =
 let source_str = Tid.name source in
 if (String.compare source_str "@start-pseudo-node") = 0 || (String.compare source_str "@exit-pseudo-node") = 0 then fun ~target->AI.bottom else
 match (Program.lookup blk_t ctx source) with
   | Some b ->
     let postcond = denote_defs b env in
     denote_jump denote_call b postcond
   | None -> invalid_arg "source tid does not represent block"


type vsa_sol = (tid, AI.t) Solution.t


(* TODO: currently assumes 64-bit architecture *)
let set_stack_0 : def term =
  let rsp = Var.create ~is_virtual:false ~fresh:false "RSP" (Type.Imm 64) in
  Def.create rsp (Bil.Int (Word.zero 64))

let default_entry () : AI.t =
  (* The precondition to entering the initial block is top, i.e. any input
     to the subroutine is possible.
  *)
  (* TODO: find a cleaner way to do this *)
  if !Utils.unsound_stack then denote_def set_stack_0 AI.top else AI.top

(* Set up the initial solution for a general VSA pass over a subroutine.
   Assumes that the inputs can be any valid values for their types.
 *)
let init_sol ?entry (sub : sub term) =
  let empty_map = Tid.Map.empty in
  let msb = Term.first blk_t sub in
  let entry_state = Option.value ~default:(default_entry ()) entry in
  let set_init sb = Map.set empty_map ~key:(Term.tid sb) ~data:entry_state in
  let base_map = Option.value_map ~default:empty_map ~f:set_init msb in
  (* Other than the first block, we assume that other blocks can only be
     reached via flow in the CFG. If the CFG is partial, this will produce
     an unsound result. (Note, however, that iterated VSA with explicit edge
     introduction can overcome this)
  *)
  Solution.create base_map AI.bottom

(* TODO: the call handling is highly unoptimal *)
let rec static_graph_vsa (stack : tid list) (ctx : Program.t) (s : Sub.t) (init : vsa_sol) : vsa_sol =
  (* TODO: improve handling of recursion *)
  let rec denote_call stack ~sub env ~target =
    match (Program.lookup sub_t ctx sub) with
    | None -> invalid_arg "sub tid does not represent a subroutine"
    | Some sub ->
      if List.mem stack (Term.tid s) ~equal:Tid.equal && List.length stack > 6 then AI.top else
        let fun_sol = static_graph_vsa (Term.tid sub::stack) ctx sub (init_sol ~entry:env sub) in
        sub
        |> Term.enum blk_t
        |> Seq.fold ~init:AI.bottom ~f: begin fun acc blk ->
          let source = Term.tid blk in
          let precond = Solution.get fun_sol source in
          AI.join acc @@
          denote_block (denote_call (Term.tid sub::stack)) ctx ~source precond ~target
        end
  in
  let s = Back_edges.label_back_edges s in
  let s = label_widening_points s in
  let cfg = Sub.to_graph s in
  (* We compute the least upper bound of our abstract representation  on the
     input graph by starting from a sound approximation for all nodes (top)
     and refining our knowledge in each iteration. Note that this approximation
     is only sound if we have the full control flow graph. However, this
     analysis can be used to construct a sound approximation when iterated with
     a pass that reifies possible edges.
     Also note that the documentation for fixpoint discusses computing a
     greatest lower bound starting from the bottom. However, it is more
     intuitive to view our lattice as having more possibilities at the top.
     Either way, the computation is the same.

     Note: Graphlib.fixpoint was introduced in version 1.4.0
  *)
  Cbat_contextual_fixpoint.fixpoint (module CFG) ~init:init ~equal:AI.equal ~merge:AI.join
    ~f:(denote_block (denote_call stack) ctx) cfg
    (* NOTE: correct behavior of the step function depends on BAP PR#802,
       which was merged into master on 3/27/2018
    *)
    ~step:(fun i n ->
        let mblk = Term.find blk_t s n in
        let should_widen : bool =
          Option.value_map ~default:false mblk
            ~f:(fun blk -> Term.has_attr blk do_widen) in
        if i > 10 && should_widen then AI.widen_join else fun _ x' -> x')

let load (sub : sub term) : vsa_sol option =
  let open Monads.Std.Monad.Option.Syntax in
  Term.enum blk_t sub
  |> Seq.delayed_fold ~init:Tid.Map.empty
    ~f:begin fun sol blk ~k ->
      Term.get_attr blk precond >>= fun ai ->
      k @@ Tid.Map.set sol ~key:(Term.tid blk) ~data:ai
    end
    ~finish:(fun m -> !!(Solution.create m AI.bottom))
