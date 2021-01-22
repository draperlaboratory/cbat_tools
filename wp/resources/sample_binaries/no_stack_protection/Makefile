SRC_DIR = src
BIN_DIR = bin

all: $(BIN_DIR)/main_1 $(BIN_DIR)/main_2

$(BIN_DIR):
	mkdir -p $@

$(BIN_DIR)/main_1: $(SRC_DIR)/main_1.c $(BIN_DIR)
	gcc -fstack-protector -Wall -g -o $@ $<

$(BIN_DIR)/main_2: $(SRC_DIR)/main_2.c $(BIN_DIR)
	gcc -fno-stack-protector -Wall -g -o $@ $<

clean:
	rm -rf $(BIN_DIR)
