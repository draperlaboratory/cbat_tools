PASS_NAME = wp

SAMPLE_BIN_DIR = ../resources/sample_binaries
API_PATH = $(shell bap --api-list-paths)

.PHONY: all build install clean verifier

all: install

build:
	bapbuild -use-ocamlfind -pkgs 'z3,bap_wp,re' -tag 'warn(A-48-44)' -I lib $(PASS_NAME).plugin

install: build verifier
	bapbundle update -desc 'Computes the weakest precondition of a subroutine given a postcondition.' $(PASS_NAME).plugin
	bapbundle install $(PASS_NAME).plugin

test: install
	ocamlbuild -r -use-ocamlfind -pkgs 'bap,z3,bap_wp,oUnit,re' -tag 'warn(A-48-44),debug,thread' -Is "lib,tests" test.native
	./test.native

verifier:
	cp api/c/cbat.h $(API_PATH)/c/cbat.h

clean:
	bapbundle remove $(PASS_NAME).plugin
	bapbuild -clean
	rm -f *.plugin
	rm -rf _build
