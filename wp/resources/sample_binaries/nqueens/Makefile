BINARIES=bin/

BASE := main

LARGEST_BOARD_SIZE := 19
SMALLEST_BOARD_SIZE := 4


NUM_RANGE := $(shell seq $(SMALLEST_BOARD_SIZE) $(LARGEST_BOARD_SIZE))
TARGETS += $(foreach N,$(NUM_RANGE),$(BINARIES)$(BASE)_$N )

.PHONY: all
all: $(TARGETS)

.PHONY: dir
dir:
	mkdir -p $(BINARIES)


$(TARGETS): $(BASE).c dir
	clang -O3 -Wall -D BOARD_SIZE=$(subst $(BINARIES)$(BASE)_,,$@) -o $@ $<

clean:
	rm -drf $(BINARIES)
