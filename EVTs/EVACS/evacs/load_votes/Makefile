#! /usr/bin/make

# Add binaries here (each name relative to top of tree!).
BINARIES+=load_votes/check_votes_bin
BINARIES+=load_votes/check_for_repeats_bin
BINARIES+=load_votes/handle_few_votes_bin

# Add any extra tests to run here (each name relative to top of tree!).
EXTRATESTS+=
# Include *_test.c automatically.
CTESTS+=$(foreach tc, $(wildcard load_votes/*_test.c), $(tc:.c=))

# This needs to come before any rules, so binaries is the default.
ifndef MASTER
  binaries tests clean dep TAGS:
	$(MAKE) -C .. $@ DIR="`pwd`"
endif # MASTER

load_votes/check_votes_bin: common/database.o common/evacs.o  load_votes/compare_votes.o load_votes/check_votes.o
load_votes/check_votes: common/database.o common/evacs.o load_votes/compare_votes.o
load_votes/check_for_repeats_bin: common/database.o common/evacs.o load_votes/compare_votes.o load_votes/check_for_repeats.o
load_votes/check_for_repeats: common/database.o common/evacs.o load_votes/compare_votes.o
load_votes/handle_few_votes_bin: common/database.o common/evacs.o load_votes/compare_votes.o load_votes/check_votes.o load_votes/handle_few_votes.o common/batch.o  common/find_errors.o 
load_votes/handle_few_votes: common/database.o common/evacs.o load_votes/compare_votes.o load_votes/check_votes.o common/batch.o
load_votes/check_votes_bin_ARGS = -lpq
load_votes/check_for_repeats_bin_ARGS = -lpq
load_votes/handle_few_votes_bin_ARGS = -lpq

load_votes/check_votes_test: common/database.o common/evacs.o load_votes/compare_votes.o 
load_votes/check_votes_test_ARGS:=-lpq
load_votes/check_for_repeats_test: common/database.o common/evacs.o load_votes/compare_votes.o
load_votes/check_for_repeats_test_ARGS:=-lpq
load_votes/handle_few_votes_test: common/database.o common/evacs.o load_votes/compare_votes.o load_votes/check_votes.o common/createtables.o common/batch.o data_entry/confirm.o
load_votes/handle_few_votes_test_ARGS:=-lpq
