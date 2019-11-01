include ../optimization_flags.mk

BASE=verifier

PROG1=$(BASE)_assume_unsat
PROG2=$(BASE)_assume_sat
PROG3=$(BASE)_nondet

all: $(PROG1) $(PROG2) $(PROG3)

%: %.c
	$(CC) $(FLAGS) -g -o $@ $<

clean:
	rm -f $(PROG1) $(PROG2) $(PROG3)
