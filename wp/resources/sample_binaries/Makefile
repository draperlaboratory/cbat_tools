SAMPLE_DIRS = $(wildcard */)
BUILD_DIRS = $(SAMPLE_DIRS:%=build-%)
CLEAN_DIRS = $(SAMPLE_DIRS:%=clean-%)

.PHONY: all clean
.PHONY: subdirs $(BUILD_DIRS)
.PHONY: subdirs $(CLEAN_DIRS)

all: $(BUILD_DIRS)
$(BUILD_DIRS):
	$(MAKE) -C $(@:build-%=%)

clean: $(CLEAN_DIRS)
$(CLEAN_DIRS):
	$(MAKE) -C $(@:clean-%=%) clean
