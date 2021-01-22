SRC_DIR = src
BIN_DIR = bin

BASE = main

LARGEST_BOARD_SIZE = 19
SMALLEST_BOARD_SIZE = 4

NUM_RANGE = $(shell seq $(SMALLEST_BOARD_SIZE) $(LARGEST_BOARD_SIZE))
TARGETS = $(foreach N,$(NUM_RANGE),$(BIN_DIR)/$(BASE)_$N)

FLAGS = -O3 -D BOARD_SIZE=$(subst $(BIN_DIR)/$(BASE)_,,$@)

all: $(TARGETS)

$(BIN_DIR):
	mkdir -p $(BIN_DIR)


$(TARGETS): $(SRC_DIR)/$(BASE).c $(BIN_DIR)
	clang $(FLAGS) -Wall -g -o $@ $<

clean:
	rm -rf $(BIN_DIR)
