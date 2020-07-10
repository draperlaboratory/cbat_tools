include ../optimization_flags.mk

BASE=main
PROG1=$(BASE)_1
PROG2=$(BASE)_2

all: $(PROG1) $(PROG1).bpj $(PROG2) $(PROG2).bpj

%: %.c
	$(CC) -Wall -g -o $@ $<

%.bpj: %
	bap $< --pass=save-project --save-project-filename=$@

clean:
	rm -f $(PROG1) $(PROG1).bpj $(PROG2) $(PROG2).bpj
