BAP_WP = lib/bap_wp
SAVE_PROJECT = plugin/save_project
WP = plugin

.PHONY: install doc test clean reinstall

install:
	$(MAKE) -C $(BAP_WP) $@.local
	$(MAKE) -C $(SAVE_PROJECT) $@
	$(MAKE) -C $(WP) $@

doc:
	$(MAKE) -C $(BAP_WP) $@

test: install
	$(MAKE) -C $(BAP_WP) $@
	$(MAKE) -C $(WP) $@

clean:
	$(MAKE) -C $(WP) $@
	$(MAKE) -C $(SAVE_PROJECT) $@
	$(MAKE) -C $(BAP_WP) $@.local

reinstall:
	$(MAKE) clean
	$(MAKE) install

