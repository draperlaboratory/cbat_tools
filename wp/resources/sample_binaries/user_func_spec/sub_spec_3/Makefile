include ../../optimization_flags.mk

SRC_DIR = src
BIN_DIR = bin

FLAGS += -Wpedantic -fno-stack-protector -z execstack

all: $(BIN_DIR)/main

$(BIN_DIR):
	mkdir -p $@

$(BIN_DIR)/%: $(SRC_DIR)/%.asm $(BIN_DIR)
	nasm -f elf64 -o $@.o $<
	gcc -Wall -g -o $@ $@.o 
	rm -rf $@.o

clean:
	rm -rf $(BIN_DIR)
