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
	# gcc -O3 -funroll-all-loops -funroll-loops --param max-predicted-iterations=100000 --param max-average-unrolled-insns=100000 --param max-unroll-times=100000 --param max-unrolled-insns=100000 --param max-variable-expansions-in-unroller=100000 --param max-modulo-backtrack-attempts=100000 --param max-completely-peeled-insns=100000 --param max-completely-peel-times=100000 -Wall -D BOARD_SIZE=$(subst $(BINARIES)$(BASE)_,,$@) -o $@ $<

	clang -O3 -Wall -D BOARD_SIZE=$(subst $(BINARIES)$(BASE)_,,$@) -o $@ $<

clean:
	rm -drf $(BINARIES)
