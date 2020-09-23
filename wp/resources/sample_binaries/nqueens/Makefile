BINARIES=bin/

BASE := main

LARGEST_BOARD_SIZE := 10
SMALLEST_BOARD_SIZE := 4


NUM_RANGE := $(shell seq $(SMALLEST_BOARD_SIZE) $(LARGEST_BOARD_SIZE))
TARGETS += $(foreach N,$(NUM_RANGE),$(BINARIES)$(BASE)_$N )

.PHONY: all
all: $(TARGETS)

.PHONY: dir
dir:
	mkdir -p $(BINARIES)


$(TARGETS): $(BASE).c dir
	gcc -O3 -funroll-all-loops -Wall -D BOARD_SIZE=$(subst $(BINARIES)$(BASE)_,,$@) -o $@ $<
# clang -O2 -Wall -D BOARD_SIZE=$(subst $(BINARIES)$(BASE)_,,$@) -o $@ $<

clean:
	rm -drf $(BINARIES)
