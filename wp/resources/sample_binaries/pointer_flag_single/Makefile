BASE=main

all: x86-64

x86-64: $(BASE)

$(BASE): $(BASE).c
	gcc -O0 -g -Wall -o $(BASE) $(BASE).c

clean:
	rm -f $(BASE)
