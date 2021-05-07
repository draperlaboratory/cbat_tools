# The following contains an example of --show="refuted-goals" causing wp to print
# an error message.

run () {
  bap wp \
      --func=main \
      --show="refuted-goals" \
      --postcond="(assert (= RAX #x0000000000000003))" \
      --user-func-spec="subroutine, (assert true), 
(assert (forall ((new_var (_ BitVec 64))) 
(=> 
 (and (bvule #x0000000000000000 new_var)
 (bvule new_var #x0000000000000007))
(= (select init_mem (bvadd init_RSI new_var)) (select mem (bvadd RDI new_var))
))))" \
    -- ./main
}


run
