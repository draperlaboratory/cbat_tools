SAMPLE_DIRS = $(wildcard */)
BUILD_DIRS = $(SAMPLE_DIRS:%=build-%)
CLEAN_DIRS = $(SAMPLE_DIRS:%=clean-%)
MAKEFLAGS += -j$(shell nproc)

all: $(BUILD_DIRS)
$(BUILD_DIRS):
	$(MAKE) -C $(@:build-%=%)

clean: $(CLEAN_DIRS)
$(CLEAN_DIRS):
	$(MAKE) -C $(@:clean-%=%) clean
