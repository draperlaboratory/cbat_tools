BASE=main

all: x86-64

x86-64: $(BASE)

$(BASE): $(BASE).c
	$(CC) -g -Wall -o $@ $<

clean:
	rm -f $(BASE)
