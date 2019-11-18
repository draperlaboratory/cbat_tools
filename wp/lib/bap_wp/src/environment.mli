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

(**

   This module represents the environment of a BIR program
   and is used when determining pre-conditions.

   It contains a Z3 context, a {!var_gen}, the association between BIR variables
   and Z3 constants, preconditions for previously visited blocks, a mapping of Z3
   variables to function calls during runtime, subroutine summaries, a handler for
   loop unrolling, and expression verification conditions.

*)

module EnvMap = Bap.Std.Var.Map

module Constr = Constraint

(** The state type which is maintained when creating preconditions. It contains, among
    other things, summaries for subroutines, the associations between BIR variables
    and Z3 constants, and preconditions for already visited blocks, if relevant. *)
type t

(** This type is used to create fresh variables when needed.
    It's internals should be irrelevant. *)
type var_gen

(** The type that specifies whether a fun_spec should calculate the
    precondition based off a summary or by inlining the function and
    visiting it with {!Precondition.visit_sub}. *)
type fun_spec_type =
  | Summary of (t -> Constr.t -> Bap.Std.Tid.t -> Constr.t * t)
  | Inline

(** Type that specifies what rules should be used when calculating
    the precondition of a subroutine. *)
type fun_spec = {
  spec_name: string;
  spec: fun_spec_type
}

(** Type that specifies what rules should be used when visiting a jump in a BIR program. *)
type jmp_spec = t -> Constr.t -> Bap.Std.Tid.t -> Bap.Std.Jmp.t -> (Constr.t * t) option

(** Type that specifies what rules should be used when calculating
    the precondition of an interrupt. *)
type int_spec = t -> Constr.t -> int -> Constr.t * t

(** The loop handling procedure for the appropriate blocks. *)
type loop_handler = {
  handle : t -> Constr.t -> start:Bap.Std.Graphs.Ir.Node.t -> Bap.Std.Graphs.Ir.t -> t
}

(** Conditions generated when exploring an expression: if it is a [Verify],
    this represents an additional proof obligation, an [Assume]
    represents an assumption, typically about the definedness of the expression. *)
type cond_type = Verify of Constr.goal | Assume of Constr.goal

(** Type that generates a Verification Condition on encountering a given pattern,
    typically a correctness constraint, like no overflow or no null dereference. *)
type exp_cond = t -> Bap.Std.Exp.t -> cond_type option

(** Creates a new environment with a sequence of subroutines in the program used
    to initialize function specs, a list of function_specs that each summarize
    the precondition for its mapped function, the default function_spec in the
    case a function does not satisfy the requirements of the other function_specs,
    a jump_spec for handling branches, an int_spec for handling interrupts, a list
    of exp_conds to satisfy, the number of times to unroll a loop, the
    architecture of the binary, the option to freshen variable names, a Z3
    context, and a variable generator. *)
val mk_env
  :  subs:Bap.Std.Sub.t Bap.Std.Seq.t
  -> specs:(Bap.Std.Sub.t -> Bap.Std.Arch.t -> fun_spec option) list
  -> default_spec:(Bap.Std.Sub.t -> Bap.Std.Arch.t -> fun_spec)
  -> jmp_spec:jmp_spec
  -> int_spec:int_spec
  -> exp_conds:exp_cond list
  -> num_loop_unroll:int
  -> arch:Bap.Std.Arch.t
  -> freshen_vars:bool
  -> Z3.context
  -> var_gen
  -> t

(** Creates a string representation of the environment. *)
val env_to_string : t -> string

(** Create a Z3 context, used to generate every Z3 expression.
    Simply defined as [Z3.mk_context []]. *)
val mk_ctx : unit -> Z3.context

(** Create a new variable generator. Two fresh variables created with the same generator
    will be distinct. *)
val mk_var_gen : unit -> var_gen

(** Get a fresh variable name, possibly prefixed by a given [name] string. *)
val get_fresh : ?name:string -> var_gen -> string

(** Set variable freshening, which will cause constraint generation to
    create fresh variables. *)
val set_freshen : t -> bool -> t

(** A reference to {!Precondition.visit_sub} that is needed in the
    loop handler of the environment simulating "open recursion". *)
val wp_rec_call :
  (t -> Constr.t -> start:Bap.Std.Graphs.Ir.Node.t -> Bap.Std.Graphs.Ir.t -> t) ref

(** Add a new binding to the environment for a bap variable to a Z3 expression,
    typically a constant. *)
val add_var : t -> Bap.Std.Var.t -> Constr.z3_expr -> t

(** Add a precondition to be associated to a block b to the environment. *)
val add_precond : t -> Bap.Std.Tid.t -> Constr.t -> t

(** Creates a verifier checker for a {!Constr.z3_expr}, returning first the assumptions, then the
    VCs. *)
val mk_exp_conds : t -> Bap.Std.Exp.t -> Constr.goal list * Constr.goal list

(** Obtains the Z3 context within a given environment. *)
val get_context : t -> Z3.context

(** Obtains the var_gen used to create fresh variables within a given environment. *)
val get_var_gen : t -> var_gen

(** Obtains the sequence of subroutines that belongs to a BIR program. *)
val get_subs : t -> Bap.Std.Sub.t Bap.Std.Seq.t

(** Obtains the var_map containing a mapping of BIR variables to Z3 variables. *)
val get_var_map : t -> Constr.z3_expr EnvMap.t

(** Looks up the Z3 variable that represents a BIR variable. *)
val get_var : t -> Bap.Std.Var.t -> Constr.z3_expr * t

(** Looks up the precondition for a given block in the environment. Currently returns
    True if the block is not yet visited. *)
val get_precondition : t -> Bap.Std.Tid.t -> Constr.t option

(** Looks up the subroutine's name given its tid. This is needed because a label to
    a subroutine loses its name when saving a BAP project as a .bpj file. *)
val get_sub_name : t -> Bap.Std.Tid.t -> string option

(** Finds the tid of a function in the environment. *)
val get_fun_name_tid : t -> string -> Bap.Std.Tid.t option

(** Look up the string name for the variable which represents a call made to a
    subroutine with a given [tid]. *)
val get_called : t -> Bap.Std.tid -> string option

(** Looks up the specification of a subroutine that is used to calculate the precondition
    of a function call. *)
val get_sub_handler : t -> Bap.Std.Tid.t -> fun_spec_type option

(** Looks up the list of jmp_specs that is used to calculate the precondition of
    jumps in a BIR program. *)
val get_jmp_handler : t -> jmp_spec

(** Looks up the specification of calculating the precondition of an interrupt. *)
val get_int_handler : t -> int_spec

(** Finds the {!loop_handler} that is used to unroll loops when it is visited in
    the BIR program. *)
val get_loop_handler :
  t -> (t -> Constr.t -> start:Bap.Std.Graphs.Ir.Node.t -> Bap.Std.Graphs.Ir.t -> t)

(** Obtains the architecture of the program. *)
val get_arch : t -> Bap.Std.Arch.t

(** Performs a fold on the map of of function names to tids to generate a
    {!Constr.z3_expr}. *)
val fold_fun_tids :
  t -> init:'a -> f:(key:string -> data:Bap.Std.Tid.t -> 'a -> 'a) -> 'a

(** Checks if the architecture is part of the x86 family. *)
val is_x86 : Bap.Std.Arch.t -> bool

(*-------- Z3 constant creation utilities ----------*)

(** Create a constant Z3 expression of a type that corresponds to a bap type, where
    the correspondence is as follows:

    - BitVector of width [w] -> BitVector of width [w]
    - Memory value with address size [a] and word size [w] ->
        Functional array from BitVector [a] to BitVector [w]. *)
val mk_z3_expr : Z3.context -> name:string -> typ:Bap.Std.Type.t -> Constr.z3_expr

(** Create a Z3 constant of the appropriate name and type, but ensure that the
    constant is "fresh" with the {!Environment.var_gen}. *)
val new_z3_expr : ?name:string -> t -> Bap.Std.Type.t -> Constr.z3_expr

(*---------------------------------------------------*)
