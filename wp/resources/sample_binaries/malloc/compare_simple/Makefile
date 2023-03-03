include ../../optimization_flags.mk

SRC_DIR = src
BIN_DIR = bin

FLAGS += -Wpedantic -fno-stack-protector -z execstack

all: $(BIN_DIR)/main_1.o $(BIN_DIR)/main_2.o

$(BIN_DIR):
	mkdir -p $@

$(BIN_DIR)/%.o: $(SRC_DIR)/%.c $(BIN_DIR)
	gcc $(FLAGS) -Wall -O0 -g -c -o $@ $<

clean:
	rm -rf $(BIN_DIR)
