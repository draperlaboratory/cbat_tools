PASS_NAME = wp

SAMPLE_BIN_DIR = ../resources/sample_binaries
SAVE_PROJECT_DIR = ./save_project
API_PATH = $(shell bap --api-list-paths)

.PHONY: all build install clean verifier save_project

all: install

build:
	bapbuild -use-ocamlfind -pkgs 'z3,bap_wp,re' -tag 'warn(A-48-44)' $(PASS_NAME).plugin

install: build verifier save_project
	bapbundle update -desc 'Computes the weakest precondition of a subroutine given a postcondition.' $(PASS_NAME).plugin
	bapbundle install $(PASS_NAME).plugin

test: install save_project
	ocamlbuild -r -use-ocamlfind -pkgs 'bap,z3,bap_wp,oUnit,re' -tag 'warn(A-48-44),debug,thread' -I tests test.native
	./test.native

verifier:
	cp api/c/cbat.h $(API_PATH)/c/cbat.h

save_project:
	$(MAKE) -C $(SAVE_PROJECT_DIR)

clean:
	$(MAKE) -C $(SAVE_PROJECT_DIR) $@
	bapbundle remove $(PASS_NAME).plugin
	bapbuild -clean
	rm -f *.plugin
	rm -rf _build
