project = bap_wp

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

test: test.unit test.performance

test.unit:
	dune runtest tests/unit

test.performance:
	dune runtest tests/performance

doc:
	dune build @doc

check.installed.findlib:
	ocamlfind query $(project)

check.installed.opam:
	opam show $(project)
