BASE=main

PROG1=$(BASE)_1
PROG2=$(BASE)_2

all: $(PROG1) $(PROG1).bpj $(PROG2) $(PROG2).bpj

$(PROG1): $(PROG1).c
	$(CC) -Wall -fstack-protector -g -o $@ $<

$(PROG2): $(PROG2).c
	$(CC) -Wall -fno-stack-protector -g -o $@ $<

%.bpj: %
	bap $< --pass=save-project --save-project-filename=$@

clean:
	rm -f $(PROG1) $(PROG1).bpj $(PROG2) $(PROG2).bpj
