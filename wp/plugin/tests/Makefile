#####################################################
# DEFAULT
#####################################################

.DEFAULT_GOAL = all

.PHONY: all
all: build test.unit test.integration

#####################################################
# BUILD
#####################################################

.PHONY: build
build:
	dune build

#####################################################
# CLEAN
#####################################################

.PHONY: clean
clean:
	dune clean

#####################################################
# TEST
#####################################################

.PHONY: test.unit
test.unit:
	dune runtest --force unit

.PHONY: test.integration
test.integration:
	dune runtest --force integration
