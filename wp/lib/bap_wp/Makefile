PROJECT := bap_wp
SHELL := /bin/bash

.PHONY: test test.unit test.performance all install uninstall clean build

ifeq ($PROJECT, $(shell dune installed-libraries | grep "bap_wp"))
IS_INSTALLED := 1
else
IS_INSTALLED := 0
endif

BUILD := _build/build_unique_id

SRC_FILES := $(wildcard **/*.ml) $(wildcard **/*.mli)

all: install

clean: uninstall clean.local

clean.local:
	dune clean

$(BUILD): $(SRC_FILES)
	dune build -p $(PROJECT)
	touch $(BUILD)

build: $(BUILD)

test: test.unit test.performance

test.unit:
	dune runtest tests/unit

test.performance:
	dune runtest tests/performance

doc:
	dune build @doc

install: $(BUILD)
	dune install

reinstall: clean uninstall install

uninstall:
	@printf "uninstalling..."
ifeq ($(IS_INSTALLED),1)
	@printf "more uninstallation"
	dune uninstall
endif
