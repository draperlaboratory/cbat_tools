PROJECT := bap_wp
SHELL=/bin/bash

.PHONY: test all install

ifeq ($(shell opam pin list | grep "bap_wp" | grep -oE "file://.*" | cut -c 8-), $(shell pwd))
IS_INSTALLED := true
else
IS_INSTALLED := false
endif

BUILD := _build/build_unique_id

SRC_FILES = $(wildcard src/*.ml) $(wildcard src/*.mli)

all: install

clean: uninstall clean.local
	rm -f build install
	rm -f $(BUILD)

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

check.installed.findlib:
	ocamlfind query $(PROJECT)

check.installed.opam:
	opam show $(PROJECT)

install: $(BUILD)
	dune install
# only needs to be added if does not already exist
ifeq ($(IS_INSTALLED),false)
	opam pin add -y .
endif

reinstall: clean install

uninstall:
ifeq ($(IS_INSTALLED),true)
	opam pin remove -y .
	dune uninstall
endif
