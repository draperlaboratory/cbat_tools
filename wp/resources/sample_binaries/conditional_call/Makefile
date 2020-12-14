prog = main
entry = main
all: clean build
clean:
	rm -rf $(prog).o
	rm -rf $(prog)
build:
	nasm -f elf64 -o $(prog).o $(prog).asm
	gcc -o $(prog) $(prog).o
	rm -rf $(prog).o
