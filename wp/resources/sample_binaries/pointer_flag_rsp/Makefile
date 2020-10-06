BASE=main

FLAGS=-nostdlib

all: $(BASE)

%: %.S
	$(CC) $(FLAGS) -o $@ $<

clean:
	rm -f $(BASE)
