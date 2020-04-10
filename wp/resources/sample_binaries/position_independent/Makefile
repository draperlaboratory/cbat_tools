BASE=main
PROG1=$(BASE)_1
PROG2=$(BASE)_2

all: $(PROG1).so $(PROG1).bpj $(PROG2).so $(PROG2).bpj

%.so: %.c
	$(CC) -fPIC -fno-stack-protector -shared -Wall -o $@ $<

%.bpj: %.so
	bap $< --pass=save-project --save-project-filename=$@

clean:
	rm -f $(PROG1).so $(PROG1).bpj $(PROG2).so $(PROG2).bpj
