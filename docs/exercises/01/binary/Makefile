BASE=main

all: x86-64

x86-64: $(BASE)

$(BASE): $(BASE).c
	$(CC) -g -Wall -Wpedantic -fno-stack-protector -z execstack -o $@ $<

clean:
	rm -f $(BASE)
