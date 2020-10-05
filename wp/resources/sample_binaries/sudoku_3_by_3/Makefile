BASE=main

all: x86-64

x86-64: $(BASE)

$(BASE): $(BASE).c
	clang -O3 -Wall -o $@ $<

clean:
	rm -f $(BASE)
