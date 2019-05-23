BASE=main

PROG1=$(BASE)_1

PROG2=$(BASE)_2

all: prog1 prog2

prog1: $(PROG1) $(PROG1).s $(PROG1).bpj

$(PROG1): $(PROG1).c
	gcc -Wall -fstack-protector -g -o $(PROG1) $(PROG1).c

$(PROG1).s: $(PROG1)
	objdump -Sd $(PROG1) > $(PROG1).s

$(PROG1).bpj: $(PROG1)
	$(MAKE) -C ../../../BAP/save_project
	bap --pass=save-project $(PROG1)

prog2: $(PROG2) $(PROG2).s $(PROG2).bpj

$(PROG2): $(PROG2).c
	gcc -Wall -fno-stack-protector -g -o $(PROG2) $(PROG2).c

$(PROG2).s: $(PROG2)
	objdump -Sd $(PROG2) > $(PROG2).s

$(PROG2).bpj: $(PROG2)
	$(MAKE) -C ../../../BAP/save_project
	bap --pass=save-project $(PROG2)

clean:
	rm -f $(PROG1) $(PROG1).s $(PROG1).bpj  $(PROG2) $(PROG2).s $(PROG2).bpj
