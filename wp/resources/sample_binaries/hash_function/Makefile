BASE=main

all: x86-64

x86-64: $(BASE)

$(BASE): $(BASE).c
	$(CC) -g -Wall -Wpedantic -o $@ $<

clean:
	rm -f $(BASE)
