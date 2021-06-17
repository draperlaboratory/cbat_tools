SRC_DIR = src
BIN_DIR = bin

all: $(BIN_DIR)/main

$(BIN_DIR):
	mkdir -p $@

$(BIN_DIR)/%: $(SRC_DIR)/%.c $(BIN_DIR)
	clang -O0 -g -o $@ $<

clean:
	rm -rf $(BIN_DIR)
