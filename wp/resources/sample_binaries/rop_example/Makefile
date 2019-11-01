BASE=main

PROG1=$(BASE)-original
PROG2=$(BASE)-rop

all: $(PROG1).bpj $(PROG2).bpj

%.bpj: %
	bap $< --pass=save-project --save-project-filename=$@

clean:
	rm -f $(PROG1).bpj $(PROG2).bpj
