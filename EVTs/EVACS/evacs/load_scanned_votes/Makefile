#! /usr/bin/make

# Add binaries here (each name relative to top of tree!).
BINARIES+=load_scanned_votes/check_scanned_votes_bin
BINARIES+=load_scanned_votes/handle_scanned_votes_bin

# Add any extra tests to run here (each name relative to top of tree!).
EXTRATESTS+=
# Include *_test.c automatically.
CTESTS+=$(foreach tc, $(wildcard load_scanned_votes/*_test.c), $(tc:.c=))

# This needs to come before any rules, so binaries is the default.
ifndef MASTER
  binaries tests clean dep TAGS:
	$(MAKE) -C .. $@ DIR="`pwd`"
endif # MASTER

load_scanned_votes/check_scanned_votes_bin: common/database.o common/evacs.o common/get_electorate_ballot_contents.o load_scanned_votes/check_scanned_votes.o
load_scanned_votes/handle_scanned_votes_bin: common/database.o common/evacs.o common/get_electorate_ballot_contents.o load_scanned_votes/scanned_votes.o load_scanned_votes/handle_scanned_votes.o
load_scanned_votes/check_scanned_votes_bin_ARGS = -lpq
load_scanned_votes/handle_scanned_votes_bin_ARGS = -lpq

#load_scanned_votes/check_scanned_votes_test: common/database.o common/evacs.o load_scanned_votes/compare_votes.o 
#load_scanned_votes/check_scanned_votes_test_ARGS:=-lpq
#load_scanned_votes/check_for_repeats_test: common/database.o common/evacs.o load_scanned_votes/compare_votes.o
#load_scanned_votes/check_for_repeats_test_ARGS:=-lpq
#load_scanned_votes/handle_scanned_votes_test: common/database.o common/evacs.o load_scanned_votes/compare_votes.o load_scanned_votes/check_scanned_votes.o common/createtables.o common/batch.o data_entry/confirm.o
#load_scanned_votes/handle_scanned_votes_test_ARGS:=-lpq

#load_scanned_votes/scanned_votes_test: common/database.o common/evacs.o load_scanned_votes/compare_votes.o load_scanned_votes/check_scanned_votes.o common/createtables.o common/batch.o data_entry/confirm.o
load_scanned_votes/scanned_votes_test: load_scanned_votes/scanned_votes_test.o common/database.o common/evacs.o common/get_electorate_ballot_contents.o load_scanned_votes/check_scanned_votes.o
load_scanned_votes/scanned_votes_test_ARGS:=-lpq
