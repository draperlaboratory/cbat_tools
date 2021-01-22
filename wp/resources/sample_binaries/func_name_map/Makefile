SRC_DIR = src
BIN_DIR = bin

all: $(BIN_DIR)/main_1 $(BIN_DIR)/main_2

$(BIN_DIR):
	mkdir -p $@

$(BIN_DIR)/%: $(SRC_DIR)/%.c $(BIN_DIR)
	gcc -Wall -g -o $@ -c $<

clean:
	rm -rf $(BIN_DIR)
