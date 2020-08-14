
BASE=main
PROG1=$(BASE)_1
PROG2=$(BASE)_2

all: $(PROG1) $(PROG1).bpj $(PROG2) $(PROG2).bpj

%: %.c
	gcc -O1 -funroll-loops -Wall -fno-stack-protector -o $@ $<

%.bpj: %
	bap $< --no-byteweight --pass=save-project --save-project-filename=$@

clean:
	rm -f $(PROG1) $(PROG1).bpj $(PROG2) $(PROG2).bpj
