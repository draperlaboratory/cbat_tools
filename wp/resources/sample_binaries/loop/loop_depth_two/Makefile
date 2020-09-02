BASE=main
PROG1=$(BASE)_1

all: $(PROG1)

%: %.c
	$(CC) -O0 -Wall $(FLAGS) -g -o $@ $<

clean:
	rm -f $(PROG1)
