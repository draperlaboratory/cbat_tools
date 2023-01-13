SHELL := /bin/bash

SAMPLE_BIN_DIR := ../resources/sample_binaries
API_PATH := $(shell bap config sysdatadir)/api
VERIFIER_LOCAL := api/c/cbat.h
VERIFIER_INSTALL_PATH := $(API_PATH)/c/cbat.h

#####################################################
# DEFAULT
#####################################################

.DEFAULT_GOAL = all

.PHONY: all
all: install

#####################################################
# CLEAN
#####################################################

.PHONY: clean
clean: uninstall
	dune clean

#####################################################
# BUILD
#####################################################

build:
	dune build -p wp @install

#####################################################
# INSTALL
#####################################################

install: build $(VERIFIER_INSTALL_PATH)
	dune install

$(VERIFIER_INSTALL_PATH): $(VERIFIER_LOCAL)
	cp $(VERIFIER_LOCAL) $(VERIFIER_INSTALL_PATH)

.PHONY: uninstall.verifier
uninstall.verifier:
	rm -f $(VERIFIER_INSTALL_PATH)

.PHONY: uninstall
uninstall: uninstall.verifier
	dune uninstall

.PHONY: reinstall
reinstall: uninstall reinstall


#####################################################
# TEST
#####################################################

test.build:
	$(MAKE) -C $(SAMPLE_BIN_DIR)

test.clean:
	$(MAKE) -C $(SAMPLE_BIN_DIR) clean

.PHONY: test
test: test.unit

.PHONY: test.unit
test.unit: install
	dune runtest --force tests/unit

.PHONY: test.integration
test.integration: install
	dune runtest --force tests/integration
