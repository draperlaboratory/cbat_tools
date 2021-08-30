# This test checks that we are correctly initialzing the memory in our
# constraint model using the .rodata input when passing the --init-mem
# flag: the information that the constant string "Hello, world" should
# have an 'H' in its first position is only possible if we've
# correctly initizalized the memory for that string constant.

# Should return UNSAT

run () {
  bap wp \
    --func=main \
    --trip-asserts \
    --use-fun-input-regs \
    --init-mem \
    -- ./bin/main
}

run
