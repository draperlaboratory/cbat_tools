CBAT_VALUE_SET = lib
PLUGIN = plugin
TESTS = unit-tests

.PHONY: install doc test clean reinstall

install:
	$(MAKE) -C $(CBAT_VALUE_SET) $@.local
	$(MAKE) -C $(PLUGIN) $@

doc:
	$(MAKE) -C $(CBAT_VALUE_SET) $@

test: install
	$(MAKE) -C $(TESTS) $@

clean:
	$(MAKE) -C $(PLUGIN) $@
	$(MAKE) -C $(CBAT_VALUE_SET) $@.local
	$(MAKE) -C $(TESTS) $@

reinstall: clean install
