BASE := hello_world

all: $(BASE)

$(BASE):
	nasm -w+all -f elf64 -o $@.o $@.asm
	ld -o $@.out $@.o

clean:
	rm -f $(BASE).out $(BASE).o
