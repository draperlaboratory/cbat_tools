include ../optimization_flags.mk

BASE=main
PROG=$(BASE)

all: $(PROG)

%: %.c
	$(CC) -Wall $(FLAGS) -g -o $@ $<

clean:
	rm -f $(PROG)
