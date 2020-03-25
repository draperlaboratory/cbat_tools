#include ../../../../cbat_tools/wp/resources/sample_binaries/optimization_flags.mk

BASE=main

all: x86-64

x86-64: $(BASE)

$(BASE): $(BASE).c
	$(CC) -g -Wall -Wpedantic -o $@ $<

clean:
	rm -f $(BASE)
