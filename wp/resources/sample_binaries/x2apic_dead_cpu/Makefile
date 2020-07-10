BASE=main
PROG1=$(BASE)_1
PROG2=$(BASE)_2

FLAGS=-nostdlib

all: $(PROG1) $(PROG1).bpj $(PROG2) $(PROG2).bpj

%: %.S
	gcc -shared -c -fno-stack-protector -o $@ $<

%.bpj: %
	bap $< --pass=save-project --save-project-filename=$@ \
        --no-glibc-runtime

clean:
	rm -f $(PROG1) $(PROG1).bpj $(PROG2) $(PROG2).bpj
