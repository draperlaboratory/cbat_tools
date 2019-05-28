PASS_NAME = save_project

.PHONY: all

all: install

build: $(PASS_NAME).ml
	ocamlbuild -use-ocamlfind -pkg 'bap' $(PASS_NAME).byte

install: $(PASS_NAME).ml
	bapbuild $(PASS_NAME).plugin
	bapbundle install $(PASS_NAME).plugin

clean:
	bapbundle remove $(PASS_NAME).plugin
	bapbuild -clean
	rm -rf _build $(PASS_NAME).byte $(PASS_NAME).plugin
