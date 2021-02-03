SRC_DIR = src
BIN_DIR = bin

all: $(BIN_DIR)/main

$(BIN_DIR):
	mkdir -p $@

$(BIN_DIR)/%.s: $(SRC_DIR)/%.c $(BIN_DIR)
	gcc -S -g -o $@ $<

$(BIN_DIR)/%: $(BIN_DIR)/%.s
	gcc -g -o $@ -c $<

clean:
	rm -rf $(BIN_DIR)
