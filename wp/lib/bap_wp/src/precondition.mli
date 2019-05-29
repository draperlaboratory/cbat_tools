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

(**

   This module exports types and utilities to create preconditions for
   BIR expressions, blocks and subroutines.


   Usage typically involves creating a new (abstract) {!Environment.t}
   value, a Z3 context and a {!Environment.var_gen} using the utility
   functions, along with the desired post-condition and calling the
   relevant [visit_foo] function.


   The resulting precondition can then be tested for satisfiability or
   provability using the Z3 Solver module.

*)

module Expr = Z3.Expr

module Arith = Z3.Arithmetic

module BV = Z3.BitVector

module Bool = Z3.Boolean

module Array = Z3.Z3Array

module Env = Environment

(** Create the Z3 BitVector zero value of width [i]. *)
val z3_expr_zero : Z3.context -> int -> Env.z3_expr

(** Create the Z3 BitVector 1 value of width [i]. *)
val z3_expr_one : Z3.context -> int -> Env.z3_expr

(** Translate a BIR binary operator to a Z3 one. *)
val binop : Z3.context -> Bap.Std.binop -> Env.z3_expr -> Env.z3_expr -> Env.z3_expr

(** Translate a BIR unary operator to a Z3 one. *)
val unop : Z3.context -> Bap.Std.unop -> Env.z3_expr -> Env.z3_expr

(** Translate a BIR cast operation into a Z3 one. *)
val cast : Z3.context -> Bap.Std.cast -> int -> Env.z3_expr -> Env.z3_expr

(** Look up the precondition for a subroutine in the given environment,
    for a given postcondition. *)
val lookup_sub : Bap.Std.Label.t -> Env.z3_expr -> Env.t -> Env.z3_expr

(** Get {e every} variable from a subroutine. *)
val get_vars : Bap.Std.Sub.t -> Bap.Std.Var.Set.t

(** For a subroutine, find the set of output variables. *)
val get_output_vars : Bap.Std.Sub.t -> Bap.Std.Var.Set.t

(** Create a constant Z3 expression of a type that corresponds to a bap type, where
    the correspondence is as follows:

    - BitVector of width [w] -> BitVector of width [w]
    - Memory value with address size [a] and word size [w] ->
        Functional array from BitVector [a] to BitVector [w]. *)
val mk_z3_expr : Z3.context -> name:string -> typ:Bap.Std.Type.t -> Env.z3_expr

(** Create a Z3 expression that denotes a load in memory [mem] at address [addr]. *)
val load_z3_mem
  :  Z3.context
  -> word_size:int
  -> mem:Env.z3_expr
  -> addr:Env.z3_expr
  -> Bap.Std.endian
  -> Env.z3_expr

(** Create a Z3 expression that denotes a write in memory [mem] at address [addr], writing
    the value [content]. *)
val store_z3_mem
  :  Z3.context
  -> word_size:int
  -> mem:Env.z3_expr
  -> addr:Env.z3_expr
  -> content:Env.z3_expr
  -> Bap.Std.endian
  -> Env.z3_expr

(** Create a Z3 constant of the appropriate name and type, but ensure that the
    constant is "fresh" with the {!Environment.var_gen}. *)
val new_z3_expr : ?name:string -> Env.t -> Bap.Std.Type.t -> Env.z3_expr

(** Translate a BAP BIR variable to a Z3 expression (by creating a constant of the same name). *)
val var_to_z3 : Z3.context -> Bap.Std.Var.t -> Env.z3_expr

(** Translates the sort of a Z3 expression from BitVector of variable width to a Boolean. *)
val bv_to_bool : Env.z3_expr -> Z3.context -> int -> Env.z3_expr

(** Translate a BAP word to a Z3 BitVector expression of the same width and value. *)
val word_to_z3 : Z3.context -> Bap.Std.Word.t -> Env.z3_expr

(** Translate a BIR expression to a Z3 expression, by a straightforward translation of the
    expression semantics, using the context for values of variables.

    Returns also the assumptions and the VCs generated by the hooks in the environment. *)
val exp_to_z3 : Bap.Std.exp -> Env.t -> Env.z3_expr * Env.z3_expr list * Env.z3_expr list

(** The default spec used when mapping subroutines to their preconditions. *)
val spec_default : Env.fun_spec

(** The default jmp spec for handling branches in a BIR program. *)
val jmp_spec_default : Env.jmp_spec

(** A jump spec that generates constraints for reaching a program point, 
    according to a map specifying whether a jump was taken or not. *)
val jmp_spec_reach : bool Bap.Std.Tid.Map.t -> Env.jmp_spec

(** The default interrupt spec for handling interrupts in a BIR program. *)
val int_spec_default : Env.int_spec

(** This spec enforces each memory read to be on a non-null address. *)
val non_null_vc : Env.exp_cond

(** This spec {e assumes} each memory read to be on a non-null address. *)
val non_null_assert : Env.exp_cond

(** Constant which determines the number of loop unrollings.

    We use the default value [!num_unroll = 5]. *)
val num_unroll : int ref

(** Creates a default environment with the default lists of function
    specs, jump specs, and interrupt specs, and an empty list of
    {!Environment.exp_conds}. Optionally takes in a sequence of subs to initialize
    the fun_specs, the number of times to unroll a loop, and a list of
    {!Environment.exp_cond}s. *)
val mk_default_env
  :  ?jmp_spec:Env.jmp_spec
  -> ?subs:Bap.Std.Sub.t Bap.Std.Seq.t
  -> ?num_loop_unroll:int
  -> ?exp_conds:Env.exp_cond list
  -> Z3.context
  -> Env.var_gen
  -> Env.t

(** Creates an environment that inlines function calls not defined in
    cbat.h.  It contains a default list of jump specs and interrupt
    specs, and an empty list of {!Environment.exp_cond}s. Takes in a sequence of subs
    of the program, and optionally the number of times to unroll a loop
    and a list of {!Environment.exp_cond}s. *)
val mk_inline_env
  :  ?num_loop_unroll:int
  -> ?exp_conds:Env.exp_cond list
  -> subs:Bap.Std.Sub.t Bap.Std.Seq.t
  -> Z3.context
  -> Env.var_gen
  -> Env.t

(** [mk_smtlib2_post env sub post] takes in a string representing a
    valid SMT-Lib-2 statement, and turns it into a valid postcondition
    to be passed to {!visit_sub}.

    The variables in the SMT-Lib statements need to appear in the
    environment. *)
val mk_smtlib2_post : Env.t -> string -> Env.z3_expr

(** Create a precondition for a given jump expression, depending on the postcondition
    and (potentially) the preconditions for the jump targets or the loop invariants.

    We do not handle indirect jumps at all: we just return the current postcondition,
    which is unsound of course. *)
val visit_jmp : Env.t -> Env.z3_expr -> Bap.Std.Jmp.t -> Env.z3_expr

(** Create a precondition for a given block element, which may be a jump, an
    assignment or a phi node. Depends on the postcondition, and the preconditions
    of other blocks or subroutines if the elt is a jump.

    Note that we are not complete for phi nodes, and
    the Z3 semantics may be weaker than the BIR semantics. *)
val visit_elt : Env.t -> Env.z3_expr -> Bap.Std.Blk.elt -> Env.z3_expr * Env.t

(** Create a precondition for a given block. Depends on the postcondition, and
    the preconditions of other blocks or subroutines if there is a jump.

    Currently we do not handle loops very well, except by suppressing all back-
    edges in the CFG. *)
val visit_block : Env.t -> Env.z3_expr -> Bap.Std.Blk.t -> Env.z3_expr * Env.t

(** Create a precondition for a given subroutine. Depends on the postcondition, and
    the preconditions of other blocks or subroutines if there is a jump.

    Currently we do not handle loops very well, except by suppressing all back-
    edges in the CFG. *)
val visit_sub : Env.t -> Env.z3_expr -> Bap.Std.Sub.t -> Env.z3_expr * Env.t

(** Checks to see if the precondition of a BIR program is [SAT], [UNSAT], or [UNKNOWN]. *)
val check : Z3.Solver.solver -> Z3.context -> Env.z3_expr -> Z3.Solver.status

(** Prints out the result from check, and if the result is [SAT], generate a model that
    represents the registers and memory values that lead to a specific program state. *)
val print_result : Z3.Solver.solver -> Z3.Solver.status -> unit

(** Adds a constraint to the Z3 solver in which var does not equal its value from
    the original Z3 model, then runs the Z3 solver again.

    This has a side effect that updates the state of the solver. The solver's state
    can be reverted back with [Z3.Solver.pop]. *)
val exclude
  :  Z3.Solver.solver
  -> Z3.context
  -> var:Env.z3_expr
  -> pre:Env.z3_expr
  -> Z3.Solver.status
