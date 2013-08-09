#! /usr/bin/make

# Add binaries here (each name relative to top of tree!)
# SIPL 2011-09-21 Removed truncate_db, convert_db, multiply_votes,
#                 remove_duplicates, recontstruct_ers, dump_prefs.
BINARIES+=tools/export_confirmed
BINARIES+=tools/export_ballots

# Add any extra tests to run here (each name relative to top of tree!).
EXTRATESTS+=

# Include *_test.c automatically.
CTESTS+=$(foreach tc, $(wildcard common/*_test.c), $(tc:.c=))

# This needs to come before any rules, so binaries is the default.
ifndef MASTER
  binaries tests clean dep TAGS:
	$(MAKE) -C .. $@ DIR="`pwd`"
endif # MASTER

tools/export_confirmed: tools/export_confirmed.o 
tools/export_confirmed_ARGS:=-lpq 

tools/export_ballots: tools/export_ballots.o 
tools/export_ballots_ARGS:=-lpq 

