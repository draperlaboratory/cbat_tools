SRC_DIR = src
BIN_DIR = bin

FLAGS = -fno-stack-protector

all: $(BIN_DIR)/main_1.so $(BIN_DIR)/main_2.so

$(BIN_DIR):
	mkdir -p $@

$(BIN_DIR)/%.so: $(SRC_DIR)/%.c $(BIN_DIR)
	gcc $(FLAGS) -Wall -g -o $@ $<

clean:
	rm -rf $(BIN_DIR)
