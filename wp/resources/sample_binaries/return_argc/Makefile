include ../optimization_flags.mk

BASE=main

all: x86-64

x86-64: $(BASE)

$(BASE): $(BASE).c
	gcc $(FLAGS) -g -Wall -Wpedantic -fno-stack-protector -z execstack -o $(BASE) $(BASE).c

$(BASE).s : $(BASE).c
	gcc -S -o $(BASE).s $(BASE).c


clean:
	rm -f $(BASE)
