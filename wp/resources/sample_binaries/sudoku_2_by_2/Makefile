SRC_DIR = src
BIN_DIR = bin

FLAGS = -O2

all: $(BIN_DIR)/main

$(BIN_DIR):
	mkdir -p $@

$(BIN_DIR)/%: $(SRC_DIR)/%.c $(BIN_DIR)
	gcc $(FLAGS) -Wall -g -o $@ $<

clean:
	rm -rf $(BIN_DIR)
