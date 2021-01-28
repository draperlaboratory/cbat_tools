# WP of Procedure Calls

Suppose we have some code

```
int foo(int x) {
  if(x == 7) return 7;
  return 4;
}

int main(int argc, char *argv[]) {
  if (argc < 4) return 4 ;
  argc = foo(argc);
  return argc;
}
```

Refinement calculus extends non-deterministic statements with the notion of specification statement. Informally, this statement represents a procedure call in black box, where the body of the procedure is not known. Say we have some procecedure `foo` with precondition `P` and postcondition `Q`, and foo has a return value `output` bound in Q. Since `RAX` is the register for outputs, we would have

  - P {foo} Q --->  RAX := output

For example, letting P = `(x != 7)` and Q = `(output == 4)`, and foo being the same as foo in the above code :

  - (x != 7) {if (x == 7)return 7;return 4} (output==4) --->  RAX := output

I.e. `foo` returns some value and that value `output` is stored in `RAX`. The value `output` is a fresh logical variable bound in Q that represents the new value of `RAX` non-deterministically chosen by the statement.

The weakest-precondition of `foo` is given by:

  - wp(P{foo}Q --->  RAX := output,R) =
    P &#8743; (&#8704; z,Q[output <- z]  => R[RAX <- z])

where `R` is the postconditon of the function that the procedure is called in (in our example, that's `main`) and `z` is a fresh name, which in CBAT is actually `<procedure-name>_ret_RAX(RDI,RSP,...)` (or in our example, it would be called `foo_ret_RAX(RDI,RSP,...)`). The inputs `RDI,RSP,...` are all the global variables we work with (like registers and other variables we make). The way we calculate &#8704; z,Q[output <- foo_ret_RAX(RDI,RSP,...)] in CBAT is by running `Precondition.subst_fun_outputs env sub Q ~inputs:[RDI,RSP,...]`.

# Keeping track of variable names

Since the problem we're trying to tackle here is dealing with constraints in a sub-routine, we need to be thoughtful about the naming of global-variables (the registers, mainly) when writing smt-lib strings. For example, if we have the code

```
(P : "RDI != 7")
int foo (int x) {
    if (x == 7) return x ;
    return x + 10;
}
(Q : "RAX_mod == RDI_orig + 10")

int main (int x) {
    x = foo(x);
    return ( x + 3 )
}
(R = "RAX_mod == foo_ret_RAX + 3")
```

Where P and Q are respectively the pre and postconditions of foo, and R is the postcondition of main. The challenge here is that the when we combine P, Q and R to create our P &#8743; (&#8704; z,Q[output <- z]  => R[RAX <- z]) mentioned earlier, we need to make sure the variables are used properly.

Since global variables can change over the course of the computation, if we want to reason about what a global variable was as opposed to what it is now, we have to introduce new variable names. For example, in the above, Q mentions `RDI_orig` to tell the difference between what RDI started as and what RDI may have changed to (a.k.a. `RDI_mod`).

# Implementation

The way this is executed in CBAT is with the following

```
let user_func_spec (user_input_name : string) (pre : string) (post : string)
    (sub : Sub.t) (arch : Arch.t) : Env.fun_spec option =
  if String.equal user_input_name (Sub.name sub) then
    (* create function that parses the pre and use Z3 to make precondition*)
    Some {
      spec_name = sub_name_EXAMPLE ;
      spec = Summary (fun env outer_post _ ->
          let string_to_constr = (fun str -> (smtlib_tokenize env env str user_input_name )
                                           |> Z3_utils.mk_smtlib2_single env) in
         let module T = (val target_of_arch arch) in
         let inputs : Var.t list = Set.elements (T.CPU.gpr) in
         (*constraintify post*)
         let post_constr : Constr.t = string_to_constr post in
         (* factor in RDI := RDI + 8 *)
         let rdi_plus = string_to_constr "(assert (= RSP_mod (bvadd RSP_orig #x0000000000000008)))" in
         (* Q => R *)
         let q_imp_r : Constr.t  = (Constr.mk_clause [rdi_plus; post_constr] [outer_post]) in
         (* forall z.(Q[output <- z] => R[output <- z]) *)
         let forall_z_qz_imp_rz : Constr.t  = subst_fun_outputs env sub q_imp_r ~inputs:inputs ~outputs:[] in
         let pre_constr : Constr.t = string_to_constr pre in
         (* (pre_constr /\ forall z.(Q[output <- z] => R[output <- z]))  *)
         let wp : Constr.t = Constr.mk_clause [pre_constr ; forall_z_qz_imp_rz] [] in
         wp , env)
    }
  else None
```

A few remarks:

Q: What does `smtlib_tokenize` do and why do we use it here?
A: `smtlib_tokenize` will convert strings like "RAX_mod" to "RAX<some-number>", like `RAX022`. This way the variable can be understood by Z3. In practice, the user writes the input as "RAX_mod/orig"
and then the string gets translated into a proper Z3 variable.

Q: What is `inputs : Var.t list = Set.elements (T.CPU.gpr)`?
A: `inputs` is the list of all global variables in BAP, like `RAX`, `RDI`, etc.

Q: What is `(assert (= RSP_mod (bvadd RSP_orig #x0000000000000008)))`?
A: That is an SMTLIB-string to keep track of the extra info that within a subroutine, the value of RSP changes. In the BIR, we would see the line `RSP := RSP + 8`. Here we add this string to the the postcondition (called `post`) because it's what we expect to be true after the end of the run of the procedure.



An example run:

Ideally we run a `.sh`-file with the following code:

```
run () {
  bap wp \
    --func=main \
    --compare-post-reg-values=RAX \
    --precond="(assert (and (= #x0000000000000000 (bvand foo_RAX #xFFFFFFFF00000000)) (not (= RAX_mod #x0000000000000007))))" \
    --user-func-spec="foo,(assert (= RDI_orig RDI_orig)),(assert (= foo_RAX_mod RAX_mod))" \
    -- main_1 main_2
}
```

CBAT would recognize that `foo_RAX` is the output of the foo-subroutine.
