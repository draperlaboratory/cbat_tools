BAP_WP = lib/bap_wp
WP = plugin
SAMPLE_BINS = resources/sample_binaries

.PHONY: install doc test clean reinstall

install:
	$(MAKE) -C $(BAP_WP) $@.local
	$(MAKE) -C $(WP) $@

doc:
	$(MAKE) -C $(BAP_WP) $@

test: install
	$(MAKE) -C $(BAP_WP) $@
	$(MAKE) -C $(WP) $@

test.clean:
	$(MAKE) -C $(SAMPLE_BINS) clean

clean:
	$(MAKE) -C $(WP) $@
	$(MAKE) -C $(BAP_WP) $@.local

reinstall: clean install
