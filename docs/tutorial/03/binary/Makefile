BASE=main
BASE_FIXED=main_fixed

all: x86-64

x86-64: $(BASE) $(BASE_FIXED)

$(BASE): $(BASE).c
	$(CC) -g -Wall -Wpedantic -fno-stack-protector -z execstack -o $@ $<

$(BASE_FIXED): $(BASE_FIXED).c
	$(CC) -g -Wall -Wpedantic -fno-stack-protector -z execstack -o $@ $<

clean:
	rm -f $(BASE)
	rm -f $(BASE_FIXED)
