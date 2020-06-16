BASE=main
PROG1=$(BASE)_1
PROG2=$(BASE)_2

FLAGS=-nostdlib -no-pie

all: $(PROG1) $(PROG1).bpj $(PROG2) $(PROG2).bpj

%: %.S
	$(CC) $(FLAGS) -o $@ $<

%.bpj: %
	bap $< --pass=save-project --save-project-filename=$@ \
        --no-glibc-runtime

clean:
	rm -f $(PROG1) $(PROG1).bpj $(PROG2) $(PROG2).bpj
