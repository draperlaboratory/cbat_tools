BASE=main

PROG1=$(BASE)_1
PROG2=$(BASE)_2

all: $(PROG1) $(PROG2)

$(PROG1): $(PROG1).c
	$(CC) -Wall -fstack-protector -g -o $@ $<

$(PROG2): $(PROG2).c
	$(CC) -Wall -fno-stack-protector -g -o $@ $<

clean:
	rm -f $(PROG1) $(PROG2)
