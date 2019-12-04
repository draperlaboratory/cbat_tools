SAMPLE_DIRS = diff_data diff_data_location diff_stack
BUILD_DIRS = $(SAMPLE_DIRS:%=build-%)
CLEAN_DIRS = $(SAMPLE_DIRS:%=clean-%)

.PHONY: all subdirs $(BUILD_DIRS)
all: $(BUILD_DIRS)
$(BUILD_DIRS):
	$(MAKE) -C $(@:build-%=%)

.PHONY: clean subdirs $(CLEAN_DIRS)
clean: $(CLEAN_DIRS)
$(CLEAN_DIRS):
	$(MAKE) -C $(@:clean-%=%) clean
