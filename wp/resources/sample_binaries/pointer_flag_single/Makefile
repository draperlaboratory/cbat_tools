BASE=main

all: x86-64

x86-64: $(BASE)

$(BASE): $(BASE).c
	gcc -O0 -g -Wall -o $(BASE) $(BASE).c

$(BASE).s : $(BASE).c
	gcc -O0 -S -o $(BASE).s $(BASE).c


clean:
	rm -f $(BASE)
