PASS_NAME := wp
SHELL := /bin/bash

SAMPLE_BIN_DIR := ../resources/sample_binaries
API_PATH := $(shell bap --api-list-paths)
VERIFIER_LOCAL := api/c/cbat.h
VERIFIER_INSTALL_PATH := $(API_PATH)/c/cbat.h

PKGS := 'z3,bap_wp,re'
TAG := 'warn(A-48-44)'
Is := 'lib'

TEST_PKGS := 'bap,z3,bap_wp,oUnit,re'
TEST_TAG := 'warn(A-48-44),debug,thread'
TEST_Is := 'lib,tests/test_libs'

TEST_Is_UNIT := $(TEST_Is)',tests/unit'
TEST_Is_INTEGRATION := $(TEST_Is)',tests/integration'

BUILD := $(PASS_NAME).plugin
SRC_FILES := $(wildcard **/*.ml) $(wildcard **/*.mli)

#####################################################
# DEFAULT
#####################################################

.DEFAULT_GOAL = all

.PHONY: all
all: install

#####################################################
# CLEAN
#####################################################

clean: uninstall test.clean
	bapbuild -clean

#####################################################
# BUILD
#####################################################

build: $(BUILD)

$(BUILD): $(SRC_FILES)
	bapbuild -use-ocamlfind -pkgs $(PKGS) -tag $(TAG) -I $(Is) $(PASS_NAME).plugin

#####################################################
# INSTALL
#####################################################

install: $(BUILD) $(VERIFIER_INSTALL_PATH)
	bapbundle update -desc 'Computes the weakest precondition of a subroutine given a postcondition.' $(PASS_NAME).plugin
	bapbundle install $(PASS_NAME).plugin

$(VERIFIER_INSTALL_PATH): $(VERIFIER_LOCAL)
	cp $(VERIFIER_LOCAL) $(VERIFIER_INSTALL_PATH)

.PHONY: uninstall.verifier
uninstall.verifier:
	rm -f $(VERIFIER_INSTALL_PATH)

.PHONY: uninstall
uninstall: uninstall.verifier
	bapbundle remove $(PASS_NAME).plugin

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
test.unit: install test.build
	ocamlbuild -r -use-ocamlfind \
		-pkgs $(TEST_PKGS) \
		-tag $(TEST_TAG) -Is $(TEST_Is_UNIT) test.native
	OUNIT_CI=true ./test.native

.PHONY: test.integration
test.integration: install test.build
	ocamlbuild -r -use-ocamlfind \
		-pkgs $(TEST_PKGS) \
		-tag $(TEST_TAG) \
		-tag $(TEST_TAG) -Is $(TEST_Is_INTEGRATION) test.native
	OUNIT_CI=true ./test.native
