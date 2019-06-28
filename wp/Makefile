BAP_WP = lib/bap_wp
WP = plugin

.PHONY: install doc test clean reinstall

install:
	$(MAKE) -C $(BAP_WP) $@.local
	$(MAKE) -C $(WP) $@

doc:
	$(MAKE) -C $(BAP_WP) $@

test:
	$(MAKE) -C $(BAP_WP) $@
	$(MAKE) -C $(WP) $@

clean:
	$(MAKE) -C $(WP) $@
	$(MAKE) -C $(BAP_WP) $@.local

reinstall: clean install
