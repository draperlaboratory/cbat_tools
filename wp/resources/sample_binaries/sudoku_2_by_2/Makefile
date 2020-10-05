BASE=main

all: x86-64

x86-64: $(BASE)

$(BASE): $(BASE).c
	gcc -O2 -Wall -o $@ $<

clean:
	rm -f $(BASE)
