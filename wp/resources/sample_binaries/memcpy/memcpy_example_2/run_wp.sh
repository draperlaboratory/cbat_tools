#!/bin/sh

run () {
  bap wp \
      --func=main \
      --precond="(assert (and 
(bvule (_ bv4 64) RDI)
(bvule RDI #x000000000000FFFF)
(= (select mem #x0000000000701050) (_ bv12 8))
))" \
      --postcond="(assert (and 
(= RAX (_ bv0 64))
(= (select mem #x0000000000701050) (_ bv12 8))
))" \
      --user-func-specs="memcpy, (assert true),
(assert (and 
(= RDI init_RDI)
(forall ((new_var (_ BitVec 64)))
   (=> (or 
            (bvuge new_var (bvadd RDI (_ bv8 64)))
      	    (bvule new_var RDI))
   (= (select init_mem new_var) (select mem new_var)) ))
(forall ((index (_ BitVec 64))) 
(=> 
(and
	(bvule (_ bv0 64) index)
	(bvult index init_RDX))
(= (select init_mem (bvadd init_RSI index)) (select mem (bvadd RDI index)))))))" \
    ./bin/main
}


run


