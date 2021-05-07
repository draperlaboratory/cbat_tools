SRC_DIR = src
BIN_DIR = bin

all: $(BIN_DIR)/main

$(BIN_DIR):
	mkdir -p $@

$(BIN_DIR)/%: $(SRC_DIR)/%.c $(BIN_DIR)
	gcc -Wall -g -o $@ -c $<

clean:
	rm -rf $(BIN_DIR)
