#This file should return SAT

run () {    
    --func=main \
    --show=regs \ 
    --user_func_spec="g,(assert true),(assert false)" \
    --trip-assert \ 
    --main
    }

run
