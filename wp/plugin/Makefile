PASS_NAME := wp
SHELL := /bin/bash

SAMPLE_BIN_DIR := ../resources/sample_binaries
API_PATH := $(shell bap --api-list-paths)
VERIFIER_LOCAL := api/c/cbat.h
VERIFIER_INSTALL_PATH := $(API_PATH)/c/cbat.h

BUILD := $(PASS_NAME).plugin
SRC_FILES := $(wildcard **/*.ml) $(wildcard **/*.mli)

.PHONY: all test uninstall uninstall.verifier

all: install

install: $(BUILD) $(VERIFIER_INSTALL_PATH)
	bapbundle update -desc 'Computes the weakest precondition of a subroutine given a postcondition.' $(PASS_NAME).plugin
	bapbundle install $(PASS_NAME).plugin

build: $(BUILD)

$(BUILD): $(SRC_FILES)
	bapbuild -use-ocamlfind -pkgs 'z3,bap_wp,re' -tag 'warn(A-48-44)' -I lib $(PASS_NAME).plugin

test.build:
	$(MAKE) -C $(SAMPLE_BIN_DIR)

test.clean:
	$(MAKE) -C $(SAMPLE_BIN_DIR) clean

test: install test.build
	ocamlbuild -r -use-ocamlfind \
		-pkgs 'bap,z3,bap_wp,oUnit,re' \
		-tag 'warn(A-48-44),debug,thread' -Is "lib,tests" test.native
	./test.native

$(VERIFIER_INSTALL_PATH): $(VERIFIER_LOCAL)
	cp $(VERIFIER_LOCAL) $(VERIFIER_INSTALL_PATH)

uninstall.verifier:
	rm -f $(VERIFIER_INSTALL_PATH)

uninstall: uninstall.verifier
	bapbundle remove $(PASS_NAME).plugin

clean: uninstall test.clean
	bapbuild -clean
