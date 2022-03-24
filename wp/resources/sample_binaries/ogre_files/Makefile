SRC_DIR = src
BIN_DIR = bin
CC = arm-linux-gnueabi-gcc


FLAGS = -Wpedantic -fno-stack-protector -z execstack

all: $(BIN_DIR)/main_1 $(BIN_DIR)/main_2 \
		 $(BIN_DIR)/main_1_stripped $(BIN_DIR)/main_2_stripped
$(BIN_DIR):
	mkdir -p $@

$(BIN_DIR)/%_stripped: $(BIN_DIR)/%
	cp $(BIN_DIR)/$* $@
	strip $@

$(BIN_DIR)/%: $(SRC_DIR)/%.c $(BIN_DIR)
	$(CC) $(FLAGS) -Wall -g -o $@ $<

clean:
	rm -rf $(BIN_DIR)
