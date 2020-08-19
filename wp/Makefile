SHELL=/bin/bash
LIB := lib/bap_wp
PLUGIN := plugin
SAMPLE_BINS := resources/sample_binaries

.PHONY: test.integration test.lib test.plugin

install: build.lib uninstall.plugin uninstall.lib install.lib build.plugin install.plugin

uninstall.lib:
	@printf "\n\u001b[31mUNINSTALLING LIB\u001b[0m\n"
	$(MAKE) -C $(LIB) uninstall

uninstall.plugin:
	@printf "\n\u001b[31mUNINSTALLING PLUGIN\u001b[0m\n"
	$(MAKE) -C $(PLUGIN) uninstall


build: build.lib build.plugin

build.lib:
	$(MAKE) -C $(LIB) $*

build.plugin: install.lib
	$(MAKE) -C $(PLUGIN) $*

doc:
	$(MAKE) -C $(LIB) $@

test: install test.lib test.plugin test.integration

test.lib:
	$(MAKE) -C $(LIB) $*

test.plugin:
	$(MAKE) -C $(SAMPLE_BINS) $*
	$(MAKE) -C $(PLUGIN) $*

test.clean:
	$(MAKE) -C $(SAMPLE_BINS) clean

clean: test.clean
	$(MAKE) -C $(PLUGIN) $@
	$(MAKE) -C $(LIB) $@

reinstall: clean install

install.plugin:
	$(MAKE) -C $(PLUGIN) $*

# lib must be installed BEFORE building plugin
install.lib:
	$(MAKE) -C $(LIB) $*
