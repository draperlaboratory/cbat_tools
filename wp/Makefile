SHELL := /bin/bash
LIB := lib/bap_wp
PLUGIN := plugin
SAMPLE_BINS := resources/sample_binaries
FMT_STR := "\u001b[31m%s\u001b[0m\n"

.PHONY: all uninstall.lib uninstall.plugin uninstall build build.lib build.plugin doc test test.lib test.plugin clean reinstall install install.plugin install.lib


# test.lib test.plugin test all clean uninstall uninstall.lib uninstall.plugin reinstall

all: install

install: uninstall.plugin install.plugin

uninstall.lib:
	@printf $(FMT_STR) "UNINSTALLING LIB"
	$(MAKE) -C $(LIB) uninstall

uninstall.plugin:
	@printf $(FMT_STR) "UNINSTALLING PLUGIN"
	$(MAKE) -C $(PLUGIN) uninstall

uninstall: uninstall.lib uninstall.plugin

build: build.lib build.plugin

build.lib:
	@printf $(FMT_STR) "BUILDING LIB"
	$(MAKE) -C $(LIB) $*

build.plugin: build.lib install.lib
	@printf $(FMT_STR) "BUILDING PLUGIN"
	$(MAKE) -C $(PLUGIN) build

doc:
	$(MAKE) -C $(LIB) $@

test: install test.lib test.plugin

test.lib:
	@printf $(FMT_STR) "TESTING LIB"
	$(MAKE) -C $(LIB) test

test.plugin:
	@printf $(FMT_STR) "TESTING PLUGIN"
	$(MAKE) -C $(PLUGIN) test

clean:
	@printf $(FMT_STR) "CLEANING LIB"
	$(MAKE) -C $(LIB) clean
	@printf $(FMT_STR) "CLEANING PLUGIN"
	$(MAKE) -C $(PLUGIN) clean


reinstall: uninstall install

install.plugin: install.lib
	@printf $(FMT_STR) "INSTALLING PLUGIN"
	$(MAKE) -C $(PLUGIN) $*

# lib must be installed BEFORE building plugin
install.lib:
	@printf $(FMT_STR) "INSTALLING LIB"
	$(MAKE) -C $(LIB) install
