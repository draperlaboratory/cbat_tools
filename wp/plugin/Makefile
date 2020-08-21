PASS_NAME := wp
SHELL=/bin/bash

SAMPLE_BIN_DIR = ../resources/sample_binaries
API_PATH = $(shell bap --api-list-paths)

BUILD := _build/build_unique_id

.PHONY: all verifier save_project test uninstall uninstall.save_project uninstall.verifier

all: install

install: save_project $(BUILD) | verifier
	bapbundle update -desc 'Computes the weakest precondition of a subroutine given a postcondition.' $(PASS_NAME).plugin
	bapbundle install $(PASS_NAME).plugin

build: $(BUILD)

$(BUILD): wp.ml
# exactly one version of bap_wp installed
ifneq ($(shell opam pin list | grep "bap_wp" | wc -l), 1)
	$(error "bap_wp lib is not installed. Please install using relevant makefile.")
endif
	bapbuild -use-ocamlfind -pkgs 'z3,bap_wp,re' -tag 'warn(A-48-44)' -I lib $(PASS_NAME).plugin
	# hack but no easy way around it
	touch $(BUILD)

test.build:
	$(MAKE) -C $(SAMPLE_BIN_DIR)

test.clean:
	$(MAKE) -C $(SAMPLE_BIN_DIR) clean

test: install save_project dummy test.build
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

uninstall.verifier:
	rm -f $(API_PATH)/c/cbat.h

uninstall: uninstall.save_project uninstall.verifier
	bapbundle remove $(PASS_NAME).plugin

clean: uninstall test.clean
	$(MAKE) -C $(SAVE_PROJECT_DIR) $@
	bapbuild -clean
	rm -f *.plugin 
	rm -rf _build
	rm -f build
