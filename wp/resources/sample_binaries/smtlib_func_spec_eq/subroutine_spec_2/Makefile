# include ../optimization_flags.mk

BASE=main
PROG1=$(BASE)

all: $(PROG1)

%: %.c
	$(CC) -Wall $(FLAGS) -g -o $@ $<

clean:
	rm -f $(PROG1)
