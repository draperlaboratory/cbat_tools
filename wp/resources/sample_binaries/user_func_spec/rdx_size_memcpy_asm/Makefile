prog = main
entry = main

all: clean build

clean:
	rm -rf $(prog).o
	rm -rf $(prog)

build:
	nasm -f elf64 -g -o $(prog).o $(prog).asm
	ld -e $(entry) -o $(prog) $(prog).o
	rm -rf $(prog).o
