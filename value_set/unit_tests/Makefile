.PHONY: test clean

all: test

test:
	ocamlbuild -r -use-ocamlfind -pkgs 'bap, cbat_value_set,oUnit' -tag 'warn(A-48-44),debug,thread' test.byte
	ocamlrun test.byte

clean:
	rm -rf _build
	rm -f test.byte
