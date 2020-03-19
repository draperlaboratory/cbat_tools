BASE=main

all: x86-64

x86-64: $(BASE)

$(BASE): $(BASE).c
	gcc -g -Wall -o $(BASE) $(BASE).c

$(BASE).s : $(BASE).c
	gcc -S -o $(BASE).s $(BASE).c


clean:
	rm -f $(BASE)
