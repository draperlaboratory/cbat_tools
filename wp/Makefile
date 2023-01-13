SHELL := /bin/bash
LIB := lib/bap_wp
PLUGIN := plugin
SAMPLE_BINS := resources/sample_binaries
FMT_STR := "\u001b[31m%s\u001b[0m\n"

#####################################################
# DEFAULT
#####################################################
.DEFAULT_GOAL = all

.PHONY: all
all: install

#####################################################
# CLEAN
#####################################################

.PHONY: clean
clean:
	@printf $(FMT_STR) "CLEANING PLUGIN"
	$(MAKE) -C $(PLUGIN) clean
	@printf $(FMT_STR) "CLEANING LIB"
	$(MAKE) -C $(LIB) clean

#####################################################
# BUILD
#####################################################

.PHONY: build
build: build.lib build.plugin

.PHONY: build.lib
build.lib:
	@printf $(FMT_STR) "BUILDING LIB"
	$(MAKE) -C $(LIB) $*

.PHONY: build.plugin
build.plugin: build.lib install.lib
	@printf $(FMT_STR) "BUILDING PLUGIN"
	$(MAKE) -C $(PLUGIN) build


#####################################################
# INSTALL
#####################################################

.PHONY: install
install: install.plugin

.PHONY: uninstall
uninstall:
	$(MAKE) uninstall.plugin
	$(MAKE) uninstall.lib

.PHONY: uninstall.lib
uninstall.lib:
	@printf $(FMT_STR) "UNINSTALLING LIB"
	$(MAKE) -C $(LIB) uninstall

.PHONY: uninstall.plugin
uninstall.plugin:
	@printf $(FMT_STR) "UNINSTALLING PLUGIN"
	$(MAKE) -C $(PLUGIN) uninstall

.PHONY: reinstall
reinstall: uninstall install

.PHONY: install.plugin
install.plugin: install.lib
	@printf $(FMT_STR) "INSTALLING PLUGIN"
	$(MAKE) -C $(PLUGIN) $*

# lib must be installed BEFORE building plugin
.PHONY: install.lib
install.lib: uninstall.plugin
	@printf $(FMT_STR) "INSTALLING LIB"
	$(MAKE) -C $(LIB) install

#####################################################
# TEST
#####################################################

.PHONY: test
test: install test.lib test.plugin

.PHONY: test.lib
test.lib:
	@printf $(FMT_STR) "TESTING LIB"
	$(MAKE) -C $(LIB) test

.PHONY: test.plugin
test.plugin:
	@printf $(FMT_STR) "TESTING PLUGIN"
	$(MAKE) -C $(PLUGIN) test.unit

.PHONY: test.plugin.integration
test.plugin.integration: install
	$(MAKE) -C $(PLUGIN) test.integration

#####################################################
# DOCS
#####################################################

.PHONY: doc
doc:
	$(MAKE) -C $(LIB) $@
