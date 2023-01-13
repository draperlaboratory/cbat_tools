PROJECT := bap_wp
SHELL := /bin/bash

ifeq (1, $(shell dune installed-libraries | grep "bap_wp" | wc -l))
IS_INSTALLED := 1
else
IS_INSTALLED := 0
endif

BUILD := _build/install/default/lib/bap_wp/bap_wp.cmxa

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

.PHONY: clean
clean: uninstall clean.local

.PHONY: clean.local
clean.local:
	dune clean

#####################################################
# BUILD
#####################################################

$(BUILD): $(SRC_FILES)
	dune build -p $(PROJECT) @install
	touch $(BUILD)

.PHONY: build
build: $(BUILD)

#####################################################
# INSTALL
#####################################################

.PHONY: install
install: $(BUILD)
	dune install

.PHONY: reinstall
reinstall:
	$(MAKE) uninstall
	$(MAKE) install

.PHONY: uninstall
uninstall:
# eq is needed otherwise errors if not installed
ifeq ($(IS_INSTALLED),1)
	dune uninstall
	opam remove .
endif

#####################################################
# TEST
#####################################################

.PHONY: test
test: test.unit test.performance

.PHONY: test.unit
test.unit:
	dune runtest --force tests/unit

.PHONY: test.performance
test.performance:
	dune runtest --force tests/performance

#####################################################
# DOCS
#####################################################

doc:
	dune build @doc
