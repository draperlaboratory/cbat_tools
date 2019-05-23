BASE := hello_world

all: $(BASE)

$(BASE):
	nasm -w+all -f elf64 -o '$(BASE).o' '$(BASE).asm'
	ld -o '$(BASE).out' '$(BASE).o'

clean:
	rm -f $(BASE).out $(BASE).o
