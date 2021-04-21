SRC_DIR = src
BIN_DIR = bin

FLAGS += -Wpedantic -fno-stack-protector -g -O1 -Wall -z execstack

all: $(BIN_DIR)/main $(BIN_DIR)/main.S

$(BIN_DIR):
	mkdir -p $@

$(BIN_DIR)/%: $(SRC_DIR)/%.c $(BIN_DIR)
	gcc $(FLAGS) -o $@ $<

$(BIN_DIR)/%.S: $(SRC_DIR)/%.c $(BIN_DIR)
	gcc $(FLAGS) -S -o $@ $<


clean:
	rm -rf $(BIN_DIR)
