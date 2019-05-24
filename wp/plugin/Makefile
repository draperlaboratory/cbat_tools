SAMPLE_BIN_DIR := ../resources/sample_binaries
SAVE_PROJECT_DIR := ./save_project
API_PATH := $(shell bap --api-list-paths)

.PHONY: all

all: wp.plugin

wp.byte: wp.ml
	ocamlbuild -use-ocamlfind -pkgs 'bap,z3,bap_wp' -tag 'warn(A-48-44),debug,thread' wp.byte

wp.plugin: wp.ml verifier
	bapbuild -use-ocamlfind -pkgs 'z3,bap_wp' -tag 'warn(A-48-44)' wp.plugin
	bapbundle install wp.plugin

test: wp.plugin save_project dummy
	ocamlbuild -r -use-ocamlfind -pkgs 'bap,z3,bap_wp,oUnit' -tag 'warn(A-48-44),debug,thread' -I tests test.byte
	ocamlrun test.byte -runner sequential

verifier:
	cp api/c/cbat.h $(API_PATH)/c/cbat.h

save_project:
	$(MAKE) -C $(SAVE_PROJECT_DIR)

dummy:
	$(MAKE) -C $(SAMPLE_BIN_DIR)/dummy

clean:
	$(MAKE) -C $(SAMPLE_BIN_DIR)/dummy clean
	bapbundle remove wp.plugin
	bapbuild -clean
	rm -f *.plugin
	rm -rf _build
