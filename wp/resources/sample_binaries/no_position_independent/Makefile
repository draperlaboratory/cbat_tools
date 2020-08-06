BASE=main
PROG1=$(BASE)_1
PROG2=$(BASE)_2

all: $(PROG1).so $(PROG2).so

%.so: %.c
	$(CC) -fno-stack-protector -Wall -o $@ $<

clean:
	rm -f $(PROG1).so $(PROG2).so
