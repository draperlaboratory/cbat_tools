open Bap.Std

module TidSet = Tid.Set
module TidMap = Tid.Map

(* This function checks for exact syntactic equality between Sub.ts.
   This means that there must exist an block-level mapping between the blocks in sub 1 and
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
val exist_isomorphism : Sub.t -> Sub.t -> bool
