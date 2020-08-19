PASS_NAME = wp
SHELL=/bin/bash

SAMPLE_BIN_DIR = ../resources/sample_binaries
API_PATH = $(shell bap --api-list-paths)

# .PHONY: all install clean verifier save_project uninstall test

install: build verifier save_project
	@printf "\n\u001b[31mINSTALLING PLUGINs\u001b[0m\n"
	bapbundle update -desc 'Computes the weakest precondition of a subroutine given a postcondition.' $(PASS_NAME).plugin
	bapbundle install $(PASS_NAME).plugin


wp.ml: ;

build: wp.ml
	@printf "\n\u001b[31mBUILDING PLUGIN\u001b[0m\n"
	bapbuild -use-ocamlfind -pkgs 'z3,bap_wp,re' -tag 'warn(A-48-44)' -I lib $(PASS_NAME).plugin
	touch build

test: install save_project dummy
	ocamlbuild -r -use-ocamlfind -pkgs 'bap,z3,bap_wp,oUnit,re' -tag 'warn(A-48-44),debug,thread' -Is "lib,tests" test.native
	./test.native

verifier:
	cp api/c/cbat.h $(API_PATH)/c/cbat.h

save_project:
	$(MAKE) -C $(SAVE_PROJECT_DIR)

dummy:
	$(MAKE) -C $(SAMPLE_BIN_DIR)/dummy

uninstall.save_project:
	$(MAKE) -C $(SAVE_PROJECT_DIR) uninstall

uninstall: uninstall.save_project
	bapbundle remove $(PASS_NAME).plugin

clean: uninstall
	$(MAKE) -C $(SAVE_PROJECT_DIR) $@
	bapbuild -clean
	rm -f *.plugin 
	rm -rf _build
	rm build
