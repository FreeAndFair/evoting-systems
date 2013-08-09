#! /usr/bin/make

# Add binaries here (each name relative to top of tree!).
BINARIES+=

# Add any extra tests to run here (each name relative to top of tree!).
EXTRATESTS+=

# Include *_test.c automatically.
CTESTS+=$(foreach tc, $(wildcard common/*_test.c), $(tc:.c=))

# This needs to come before any rules, so binaries is the default.
ifndef MASTER
  binaries tests clean dep TAGS:
	$(MAKE) -C .. $@ DIR="`pwd`"
endif # MASTER

# Database test needs Postgres lib.
common/database_test: common/evacs.o common/batch.o common/createtables.o common/database.o
common/createtables_test:  common/evacs.o common/batch.o common/createtables.o common/database.o
common/batch_test:  common/evacs.o common/batch.o common/createtables.o common/database.o
common/database_test_ARGS:=-lpq
common/createtables_test_ARGS:=-lpq
common/batch_test_ARGS:=-lpq
common/barcode_hash_test_ARGS:=-lcrypto
common/barcode_hash_test: common/barcode.o

common/http_test: common/socket.o common/ballot_contents.o

common/find_errors_test:  common/evacs.o

common/ballot_contents_test:  common/ballot_contents.o common/evacs.o common/database.o  common/createtables.o
common/ballot_contents_test_ARGS:=-lpq



