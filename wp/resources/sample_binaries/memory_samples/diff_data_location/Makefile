BASE=main
PROG1=$(BASE)_1
PROG2=$(BASE)_2

FLAGS=-nostdlib -no-pie

all: $(PROG1) $(PROG2)

%: %.S
	$(CC) $(FLAGS) -o $@ $<

clean:
	rm -f $(PROG1) $(PROG2)
