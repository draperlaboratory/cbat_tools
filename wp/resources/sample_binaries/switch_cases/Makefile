BASE=main

PROG1=$(BASE)_1

PROG2=$(BASE)_2

all: prog1 prog2

prog1: $(PROG1) $(PROG1).s $(PROG1).bpj

$(PROG1): $(PROG1).c
	gcc -Wall -g -o $(PROG1) $(PROG1).c

$(PROG1).s: $(PROG1)
	objdump -Sd $(PROG1) > $(PROG1).s

$(PROG1).bpj: $(PROG1)
	bap $(PROG1) --pass=save-project --save-project-filename=$@ --no-byteweight

prog2: $(PROG2) $(PROG2).s $(PROG2).bpj

$(PROG2): $(PROG2).c
	gcc -Wall -g -o $(PROG2) $(PROG2).c

$(PROG2).s: $(PROG2)
	objdump -Sd $(PROG2) > $(PROG2).s

$(PROG2).bpj: $(PROG2)
	bap $(PROG2) --pass=save-project --save-project-filename=$@ --no-byteweight

clean:
	rm -f $(PROG1) $(PROG1).s $(PROG1).bpj  $(PROG2) $(PROG2).s $(PROG2).bpj
