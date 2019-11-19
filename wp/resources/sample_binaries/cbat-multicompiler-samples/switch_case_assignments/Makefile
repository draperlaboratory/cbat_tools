
BASE=switch_case_assignments

PROG1=$(BASE)-23908

PROG2=$(BASE)-26471

PROG3=$(BASE)-27596

PROG4=$(BASE)-28527

PROG5=$(BASE)-8458

all: prog1 prog2 prog3 prog4 prog5

prog1: $(PROG1).bpj

$(PROG1).bpj: $(PROG1)
	bap $(PROG1) --pass=save-project --save-project-filename=$(PROG1).bpj --no-byteweight

prog2: $(PROG2).bpj

$(PROG2).bpj: $(PROG2)
	bap $(PROG2) --pass=save-project --save-project-filename=$(PROG2).bpj --no-byteweight

prog3: $(PROG3).bpj

$(PROG3).bpj: $(PROG3)
	bap $(PROG3) --pass=save-project --save-project-filename=$(PROG3).bpj --no-byteweight

prog4: $(PROG4).bpj

$(PROG4).bpj: $(PROG4)
	bap $(PROG4) --pass=save-project --save-project-filename=$(PROG4).bpj --no-byteweight

prog5: $(PROG5).bpj

$(PROG5).bpj: $(PROG5)
	bap $(PROG5) --pass=save-project --save-project-filename=$(PROG5).bpj --no-byteweight

clean:
	rm -f $(PROG1).bpj $(PROG2).bpj $(PROG3).bpj $(PROG4).bpj $(PROG5).bpj
