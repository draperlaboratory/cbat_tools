include ../../../optimization_flags.mk

SRC_DIR = src
BIN_DIR = bin

FLAGS += -O0 -Wpedantic -fno-stack-protector -z execstack

all: $(BIN_DIR)/main_1 $(BIN_DIR)/main_2

$(BIN_DIR):
	mkdir -p $@

$(BIN_DIR)/%: $(SRC_DIR)/%.c $(BIN_DIR)
	gcc $(FLAGS) -Wall -g -o $@ $<

clean:
	rm -rf $(BIN_DIR)
