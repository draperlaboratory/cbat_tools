project := bap_wp
SHELL=/bin/bash

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

clean.local:
	dune clean

$(ML_FILES): ;
$(MLI_FILES): ;

build: $(ML_FILES) $(MLI_FILES)
	@printf "\n\u001b[31mBUILDING LIB\u001b[0m\n"
	dune build -p $(project)
	touch build
	echo $?

test: test.unit test.performance

test.unit:
	dune runtest tests/unit
	@echo "skipping for now"

test.performance:
	dune runtest tests/performance
	@echo "skipping for now"

doc:
	dune build @doc

check.installed.findlib:
	ocamlfind query $(project)

check.installed.opam:
	opam show $(project)

install: hack
	@printf "\n\u001b[31mINSTALLING LIB\u001b[0m\n"
	dune install
	opam pin add -y .
	touch install

hack: build
ifeq ($(IS_INSTALLED),true)
	@printf "\n\u001b[31mUNINSTALLING LIB\u001b[0m\n"
	opam pin remove -y .
	dune uninstall
endif
	touch hack

reinstall: clean install

uninstall:
ifeq ($(IS_INSTALLED),true)
	@printf "\n\u001b[31mUNINSTALLING LIB\u001b[0m\n"
	opam pin remove -y .
	dune uninstall
endif
