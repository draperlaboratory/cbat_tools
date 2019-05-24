OPTIMIZATION_LEVEL := -O2

NO_INLINE_FLAGS := -fno-indirect-inlining -fno-inline -fno-inline-atomics \
	-fno-inline-functions-called-once -fno-inline-small-functions

NO_LOOP_FLAGS := -fno-aggressive-loop-optimizations -fno-move-loop-invariants \
	-fno-prefetch-loop-arrays -fno-rerun-cse-after-loop -fno-tree-loop-if-convert \
	-fno-tree-loop-im -fno-tree-loop-ivcanon -fno-tree-loop-optimize

NO_BRANCH_FLAGS := -fno-branch-count-reg -fno-guess-branch-probability

NO_IPA_FLAGS := -fno-ipa-cp -fno-ipa-cp-alignment -fno-ipa-icf \
	-fno-ipa-icf-functions -fno-ipa-icf-variables -fno-ipa-profile -fno-ipa-pure-const \
	-fno-ipa-ra -fno-ipa-reference -fno-ipa-sra

NO_UNWIND_FLAGS := -fno-split-ivs-in-unroller -fno-unwind-tables \
	-fno-asynchronous-unwind-tables

NO_JUMP_FLAGS := -fno-crossjumping -fno-cse-follow-jumps -fno-thread-jumps

FLAGS := $(OPTIMIZATION_LEVEL) $(NO_INLINE_FLAGS) $(NO_LOOP_FLAGS) $(NO_IPA_FLAGS) \
	$(NO_UNWIND_FLAGS) $(NO_JUMP_FLAGS)
