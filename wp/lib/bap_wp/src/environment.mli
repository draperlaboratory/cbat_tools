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

module ExprSet : Core_kernel.Set.S with type Elt.t = Constr.z3_expr

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

(** Type that specifies what rules should be used when encountering an indirect call *)
type indirect_spec = t -> Constr.t -> Bap.Std.Exp.t -> bool -> Constr.t * t

(** Type that specifies what rules should be used when visiting a jump in a BIR program. *)
type jmp_spec = t -> Constr.t -> Bap.Std.Tid.t -> Bap.Std.Jmp.t -> (Constr.t * t) option

(** Type that specifies what rules should be used when calculating
    the precondition of an interrupt. *)
type int_spec = t -> Constr.t -> int -> Constr.t * t

(** The loop handling procedure for the appropriate blocks. *)
type loop_handler = {
  handle : t -> Constr.t -> start:Bap.Std.Graphs.Ir.Node.t -> Bap.Std.Graphs.Ir.t -> t
}

(** Condition generated when exploring an expression: [BeforeExec] will generate a
    {! Constr.goal} to be added to the postcondition before any substitution is made,
    and [AfterExec] will generate the goal to be added after all substitutions are
    completed. *)
type cond = BeforeExec of Constr.goal | AfterExec of Constr.goal

(** Conditions generated when exploring an expression: if it is a [Verify],
    this represents an additional proof obligation, an [Assume]
    represents an assumption, typically about the definedness of the expression. *)
type cond_type = Verify of cond | Assume of cond

(** Type that generates a Verification Condition on encountering a given pattern,
    typically a correctness constraint, like no overflow or no null dereference. *)
type exp_cond = t -> Bap.Std.Exp.t -> cond_type option

(* The range of addresses for a modelled memory region. The base address is the
   highest address on the stack, but the lowest address in the data section. The
   memory size is represented in bytes. *)
type mem_range = {
  base_addr : int;
  size : int
}

(** Creates a new environment with
    - a sequence of subroutines in the program used to initialize function specs
    - a list of {!fun_spec}s that each summarize the precondition for its mapped function
    - the default fun_spec in the case a function does not satisfy the requirements
      of the other fun_specs
    - a {!indirect_spec} for handling indirect calls
    - a {!jmp_spec} for handling branches
    - an {!int_spec} for handling interrupts
    - a list of {!exp_cond}s to satisfy
    - the number of times to unroll a loop
    - the architecture of the binary
    - the option to freshen variable names
    - the option to use all input registers when generating function symbols at a call site
    - the concrete range of addresses of the stack
    - the concrete range of addresses of the data section
    - a Z3 context
    - and a variable generator. *)
val mk_env
  :  subs:Bap.Std.Sub.t Bap.Std.Seq.t
  -> specs:(Bap.Std.Sub.t -> Bap.Std.Arch.t -> fun_spec option) list
  -> default_spec:(Bap.Std.Sub.t -> Bap.Std.Arch.t -> fun_spec)
  -> indirect_spec:indirect_spec
  -> jmp_spec:jmp_spec
  -> int_spec:int_spec
  -> exp_conds:exp_cond list
  -> num_loop_unroll:int
  -> arch:Bap.Std.Arch.t
  -> freshen_vars:bool
  -> use_fun_input_regs:bool
  -> stack_range:mem_range
  -> data_section_range:mem_range
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

(** Add a z3 expression representing a constant generated during the analysis to
    the environment. *)
val add_const : t -> Constr.z3_expr -> t

(** Removes all z3 expressions representing constants from the environment. This is used
    because the initial pass through a binary generates constants that are not
    used during precondition computation. *)
val clear_consts : t -> t

(** A reference to {!Precondition.visit_sub} that is needed in the
    loop handler of the environment simulating "open recursion". *)
val wp_rec_call :
  (t -> Constr.t -> start:Bap.Std.Graphs.Ir.Node.t -> Bap.Std.Graphs.Ir.t -> t) ref

(** Add a new binding to the environment for a bap variable to a Z3 expression,
    typically a constant. *)
val add_var : t -> Bap.Std.Var.t -> Constr.z3_expr -> t

(** Remove a binding in the environment for a bap variable. *)
val remove_var : t -> Bap.Std.Var.t -> t

(** Looks up the Z3 variable that represents a BIR variable. *)
val find_var : t -> Bap.Std.Var.t -> Constr.z3_expr option

(** Add a precondition to be associated to a block b to the environment. *)
val add_precond : t -> Bap.Std.Tid.t -> Constr.t -> t

(** Creates a list of assumptions and verification conditions as hooks on an expression
    being visited during analysis. *)
val mk_exp_conds : t -> Bap.Std.Exp.t -> cond_type list

(** Obtains the Z3 context within a given environment. *)
val get_context : t -> Z3.context

(** Obtains the var_gen used to create fresh variables within a given environment. *)
val get_var_gen : t -> var_gen

(** Obtains the sequence of subroutines that belongs to a BIR program. *)
val get_subs : t -> Bap.Std.Sub.t Bap.Std.Seq.t

(** Obtains the var_map containing a mapping of BIR variables to Z3 variables. *)
val get_var_map : t -> Constr.z3_expr EnvMap.t

(* FIIL ME IN *)
val get_sub_var_map : t -> Constr.z3_expr EnvMap.t

(* FIIL ME IN *)
val get_sub_init_var_map : t -> Constr.z3_expr EnvMap.t

(** Obtains the var_map containing a mapping of BIR variables to the Z3 variables
    that represent their initial states. *)
val get_init_var_map : t -> Constr.z3_expr EnvMap.t

(** Looks up the Z3 variable that represents a BIR variable. Produces fresh z3_expr if not found. *)
val get_var : t -> Bap.Std.Var.t -> Constr.z3_expr * t

(** Looks up the precondition for a given block in the environment. Currently returns
    True if the block is not yet visited. *)
val get_precondition : t -> Bap.Std.Tid.t -> Constr.t option

(** Looks up the subroutine's name given its tid. *)
val get_sub_name : t -> Bap.Std.Tid.t -> string option

(** Finds the tid of a function in the environment. *)
val get_fun_name_tid : t -> string -> Bap.Std.Tid.t option

(** Look up the string name for the variable which represents a call made to a
    subroutine with a given [tid]. *)
val get_called : t -> Bap.Std.tid -> string option

(** Looks up the specification of a subroutine that is used to calculate the precondition
    of a function call. *)
val get_sub_handler : t -> Bap.Std.Tid.t -> fun_spec_type option

(** Looks up the indirect call spec for an expression. Used to calculate the precondition
    of an indirect call. *)
val get_indirect_handler : t -> Bap.Std.Exp.t -> indirect_spec


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

(** Obtains the general purpose registers of the architecture of the program. *)
val get_gprs : t -> Bap.Std.Var.Set.t

(** Obtains the name of the program's stack pointer *)
val get_sp: t -> Bap.Std.Var.t

(** Obtains the BAP variable representing a program's memory. *)
val get_mem : t -> Bap.Std.Var.t

(** Obtains a list of all the {!Constr.z3_expr}s that represents constants that
    were generated during analysis. *)
val get_consts : t -> ExprSet.t

(** Performs a fold on the map of of function names to tids to generate a
    {!Constr.z3_expr}. *)
val fold_fun_tids :
  t -> init:'a -> f:(key:string -> data:Bap.Std.Tid.t -> 'a -> 'a) -> 'a

(** Checks if the architecture is part of the x86 family. *)
val is_x86 : Bap.Std.Arch.t -> bool

(** Checks to see if the environment supports using all possible input registers
    when generating symbols in the function specs at a function call site. *)
val use_input_regs : t -> bool

(** [in_stack env addr] is the constraint [STACK_MIN < addr <= STACK_MAX] as
    defined by the concrete range of the stack in the env. *)
val in_stack : t -> Constr.z3_expr -> Constr.z3_expr

(** [get_stack_end] retrieves the address of the largest address that the top
     of the stack can take. It is assumed the stack grows downwards, from
     high addresss to low address. The top and start of the stack is defined as
     stack_base and is the largest address in the stack. The stack end
     (retrieved by this function) is the smallest value that the stack pointer
     can take. *)
val get_stack_end: t -> int

(** [in_data_section env addr] is the constraint [DATA_MIN <= addr < DATA_MAX] as
    defined by the concrete range of the data section in the env. *)
val in_data_section : t -> Constr.z3_expr -> Constr.z3_expr

(** [init_stack_ptr env ptr] initializes the constraint
    [STACK_MIN + 128 < sp <= STACK_MAX] which is the region of the stack that
    the stack pointer may point to at the beginning of a subroutine. The 128
    is based off of the 128 bytes of red zone underneath the stack pointer in
    x86_64. *)
val init_stack_ptr : t -> Constr.z3_expr -> Constr.z3_expr

(** [update_stack_base range base] updates the highest address of the stack to
    be the same value as base. *)
val update_stack_base : mem_range -> int -> mem_range

(** [update_stack_size range size] updates the size of the stack to be the
    same value as size. *)
val update_stack_size : mem_range -> int -> mem_range

(** [mk_init_var env var] creates a fresh Z3 variable that represents the
    initial state of variable [var]. Adds a new binding to [env] for the bap
    variable to is generated init variable. *)
val mk_init_var : t -> Bap.Std.Var.t -> Constr.z3_expr * t

(** [get_init_var var] obtains the Z3 expression that represents the initial state
    of a bap variable [var]. *)
val get_init_var : t -> Bap.Std.Var.t -> Constr.z3_expr option

(** [trivial_constr] generates a trivial constraint of just [true]. *)
val trivial_constr : t -> Constr.t

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
