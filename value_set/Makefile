SETUP = ocaml setup.ml


build: setup.ml setup.data
	$(SETUP) -build $(BUILDFLAGS)

doc: setup.ml setup.data build
	$(SETUP) -doc $(DOCFLAGS)

test: setup-tests build
	$(SETUP) -test $(TESTFLAGS)


install: setup.ml setup.data
	$(SETUP) -install $(INSTALLFLAGS)
	make plugin

uninstall: setup.ml setup.data
	$(SETUP) -uninstall $(UNINSTALLFLAGS)

plugin: setup.ml
	make -C plugin

reinstall: setup.ml
	make uninstall;
	make install

clean: setup.ml
	$(SETUP) -clean $(CLEANFLAGS)

distclean: setup.ml
	$(SETUP) -distclean $(DISTCLEANFLAGS)

setup-tests: setup.ml
	$(SETUP) -configure --enable-tests $(CONFIGUREFLAGS)

setup.data: setup.ml
	$(SETUP) -configure $(CONFIGUREFLAGS)

configure: setup.ml
	$(SETUP) -configure $(CONFIGUREFLAGS)

setup.ml:
	oasis setup

.PHONY: build doc test all install uninstall reinstall clean distclean configure plugin setup-tests

OCI=ocp-indent

.PHONY: check
check: check-ocp-indent

.PHONY: check-ocp-indent
check-ocp-indent: *.ml
	for mlfile in $^; do $(OCI) $$mlfile | diff - $$mlfile; done

.PHONY: auto-ocp-indent
auto-ocp-indent: *.ml
	for mlfile in $^; do $(OCI) -i $$mlfile; done
