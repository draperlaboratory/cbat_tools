include ../optimization_flags.mk

BASE=verifier

PROG1=$(BASE)_assume_unsat
PROG2=$(BASE)_assume_sat
PROG3=$(BASE)_nondet

all: prog1 prog2 prog3

prog1:
	gcc $(FLAGS) -g -o $(PROG1) $(PROG1).c

prog2:
	gcc $(FLAGS) -g -o $(PROG2) $(PROG2).c

prog3:
	gcc $(FLAGS) -g -o $(PROG3) $(PROG3).c

clean:
	rm -f $(PROG1) $(PROG2) $(PROG3)
