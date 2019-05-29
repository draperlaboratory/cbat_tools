project = cbat_value_set

all: build

clean.local:
	opam pin remove -y .
	dune uninstall
	dune clean

build:
	dune build -p $(project)

install.local: build
	dune install
	opam pin add -y .

doc:
	dune build @doc

check.installed.findlib:
	ocamlfind query $(project)

check.installed.opam:
	opam show $(project)
