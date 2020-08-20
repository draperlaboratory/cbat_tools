PROJECT := bap_wp
SHELL=/bin/bash

.PHONY: test all install

ifeq ($(shell opam pin list | grep "bap_wp" | grep -oE "file://.*" | cut -c 8-), $(shell pwd))
IS_INSTALLED := true
else
IS_INSTALLED := false
endif

ML_FILES = $(wildcard src/*.ml)
MLI_FILES = $(wildcard src/*.mli)

all: install

clean: uninstall clean.local
	rm -f build install
	rm -f _build/build

clean.local:
	dune clean

build: $(ML_FILES) $(MLI_FILES)
	dune build -p $(PROJECT)

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

install: build
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
