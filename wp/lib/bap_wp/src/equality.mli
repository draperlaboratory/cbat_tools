open Bap.Std

(* This function checks for exact syntactic equality between Sub.ts.
    It returns the map (if it exists) from the block level tids in the first
    sub to the second sub.
   This means that there must exist an block-level mapping
    between the blocks in sub 1 and
    in sub 2 such that syntax matches. Syntax includes several things:
   - the base of physical variable names
   - structure including control flow and phi terms (of which there should be none)
   - the usage of variables in the subs must match. E.g. if I have in sub 1:
        #45 := RBP
        mem := mem with [RSP, el]:u64 <- #45
     and
        #88 := RBP
        mem := mem with [RSP, el]:u64 <- #88
     Then these two blocks (and the entire sub.ts if they were to consist only of this)
     would match. However, if instead we had something like:
        #45 := RBP
        mem := mem with [RSP, el]:u64 <- #45
     and
        #88 := RBP
        mem := mem with [RSP, el]:u64 <- #90
     then the blocks would not be syntactically equal since #45 would be expected
     in the spot that #90 is taking.
   - The block TIDs mentioned within jmp_ts in sub1 when run through the
     constructed block mapping must match the corresponding TIDS
     in the same respective jmp_t in sub2.
*)
val exist_isomorphism : Sub.t -> Sub.t -> (Tid.t Tid.Map.t) option

(* Compares a sub to another sub; returns a map from tid into sub1
   to the set of sub2 tids that are syntactically equal to in structure,
    variables, and syntax. Does NOT check that jmp target TIDs match. Also returns
   a map from (tid_blk_sub1, tid_blk_sub2) to the mapping between variables
   that must be equivalent used in those subs. *)
val compare_blocks_syntax : Sub.t -> Sub.t -> (Tid.Set.t Tid.Map.t) *
                                              (((Var.t Var.Map.t) Tid.Map.t) Tid.Map.t)
