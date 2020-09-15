BASE=main
PROG_1=$(BASE)_1
PROG_2=$(BASE)_2

all: $(PROG_1) $(PROG_2)

%: %.c
	$(CC) -Wall -g -o $@ $<

clean:
	rm -f $(PROG_1) $(PROG_2)
