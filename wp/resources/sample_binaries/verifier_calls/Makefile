include ../optimization_flags.mk

SRC_DIR = src
BIN_DIR = bin

all: $(BIN_DIR)/verifier_assume_unsat $(BIN_DIR)/verifier_assume_sat $(BIN_DIR)/verifier_nondet

$(BIN_DIR):
	mkdir -p $@

$(BIN_DIR)/%: $(SRC_DIR)/%.c $(BIN_DIR)
	gcc $(FLAGS) -Wall -g -o $@ $<

clean:
	rm -rf $(BIN_DIR)
