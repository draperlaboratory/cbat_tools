include ../optimization_flags.mk

BASE=main

all: x86-64

x86-64: $(BASE)

$(BASE): $(BASE).c
	$(CC) $(FLAGS) -g -Wall -Wpedantic -fno-stack-protector -z execstack -o $@ $<

clean:
	rm -f $(BASE)
