BASE=main

PROG1=$(BASE)-original

PROG2=$(BASE)-rop

all: $(PROG1).bpj $(PROG2).bpj

$(PROG1).bpj:
	bap --pass=save-project --save-project-filename=$(PROG1).bpj $(PROG1)

$(PROG2).bpj:
	bap --pass=save-project --save-project-filename=$(PROG2).bpj $(PROG2)

clean:
	rm -f $(PROG1).bpj $(PROG2).bpj
