PASS_NAME = value_set

.PHONY: all build install clean

all: install

build: $(PASS_NAME).ml
	bapbuild -use-ocamlfind -pkg 'cbat_value_set' -tag 'warn(A-48-44)' $(PASS_NAME).plugin

install: build
	bapbundle update -desc 'Performs value-set analysis on binaries' $(PASS_NAME).plugin
	bapbundle install $(PASS_NAME).plugin

clean:
	bapbundle remove $(PASS_NAME).plugin
	bapbuild -clean
	rm -f *.plugin
	rm -rf _build
