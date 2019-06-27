BASE=main
PROG1=$(BASE)_1
PROG2=$(BASE)_2

FLAGS=-nostdlib

all: prog1 prog2

prog1: $(PROG1) $(PROG1).bpj

$(PROG1): $(PROG1).S
	$(CC) $(FLAGS) -o $(PROG1) $(PROG1).S

$(PROG1).bpj: $(PROG1)
	bap --pass=save-project $(PROG1)

prog2: $(PROG2) $(PROG2).bpj

$(PROG2): $(PROG2).S
	gcc -Wall $(FLAGS) -o $(PROG2) $(PROG2).S

$(PROG2).bpj: $(PROG2)
	bap --pass=save-project $(PROG2)

clean:
	rm -f $(PROG1) $(PROG1).bpj $(PROG2) $(PROG2).bpj
