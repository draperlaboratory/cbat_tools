SRC_DIR = src
BIN_DIR = bin

all: $(BIN_DIR)/main_1.o $(BIN_DIR)/main_2.o

$(BIN_DIR):
	mkdir -p $@

$(BIN_DIR)/%.o: $(SRC_DIR)/%.c $(BIN_DIR)
	gcc -Wall -O0 -g -c -o $@ $<

clean:
	rm -rf $(BIN_DIR)
