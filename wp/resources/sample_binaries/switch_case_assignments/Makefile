BASE=main
PROG1=$(BASE)_1
PROG2=$(BASE)_2

all: $(PROG1) $(PROG2)

%: %.c
	$(CC) -g -o $@ $<

clean:
	rm -f $(PROG1) $(PROG2)
