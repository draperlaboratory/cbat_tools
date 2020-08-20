PASS_NAME := wp
SHELL=/bin/bash

SAMPLE_BIN_DIR = ../resources/sample_binaries
API_PATH = $(shell bap --api-list-paths)

BUILD := _build/build_unique_id

.PHONY: all verifier save_project test

all: install

install: verifier save_project $(BUILD)
	bapbundle update -desc 'Computes the weakest precondition of a subroutine given a postcondition.' $(PASS_NAME).plugin
	bapbundle install $(PASS_NAME).plugin

build: $(BUILD)

$(BUILD): wp.ml
	bapbuild -use-ocamlfind -pkgs 'z3,bap_wp,re' -tag 'warn(A-48-44)' -I lib $(PASS_NAME).plugin
	# hack but no easy way around it
	touch $(BUILD)

test: install save_project dummy
	ocamlbuild -r -use-ocamlfind \
		-pkgs 'bap,z3,bap_wp,oUnit,re' \
		-tag 'warn(A-48-44),debug,thread' -Is "lib,tests" test.native
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
	rm -f build
