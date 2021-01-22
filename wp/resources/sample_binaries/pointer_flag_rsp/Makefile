SRC_DIR = src
BIN_DIR = bin

FLAGS = -nostdlib

all: $(BIN_DIR)/main

$(BIN_DIR):
	mkdir -p $@

$(BIN_DIR)/%: $(SRC_DIR)/%.S $(BIN_DIR)
	gcc $(FLAGS) -Wall -g -o $@ $<

clean:
	rm -rf $(BIN_DIR)
