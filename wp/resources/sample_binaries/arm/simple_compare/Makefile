SRC_DIR = src
BIN_DIR = bin

all: $(BIN_DIR)/main.o

$(BIN_DIR):
	mkdir -p $@

$(BIN_DIR)/%.o: $(SRC_DIR)/%.asm $(BIN_DIR)
	arm-linux-gnueabi-as -g -o $@ -c $<

clean:
	rm -rf $(BIN_DIR)
