#! /usr/bin/make

# Master makefile for EVACS.
MASTER:=1

# C compilation flags.
# eVACS 2008 has:
#  CFLAGS:=-Wall -Wwrite-strings -Wmissing-prototypes -mcpu=i486 -O3 #-g -Wundef
CFLAGS:=-Werror -Wall -Wwrite-strings -Wmissing-prototypes #-g -Wundef

# Timeout (seconds) for each test.
TIMEOUT:=60

DIRS:=backup/ common/ counting/ data_correction/ data_entry/ load_scanned_votes/ load_votes/ setup_election/ setup_polling_place/ voting_client/ voting_client_stripped/ voting_server/ tools/

default: binaries

ifndef DIR
  # Include all the other makefiles (recursively).
  include $(shell find $(DIRS) -name Makefile)
else
  # Include this specific directory only.
  include $(DIR)/Makefile
endif

binaries: $(BINARIES)

RUN_TESTS:=$(foreach test, $(CTESTS) $(EXTRATESTS), $(test)-run)

# Create tests (for CTESTS) run them all.
tests: test-start $(CTESTS) $(RUN_TESTS) test-end

# SIPL 2011-09-26 Mention election_night explicitly, as it
#   is not otherwise cleaned.
EXTRA_DIRS:=election_night
clean:
	@rm -rf $(BINARIES) $(CTESTS)
        # If we're only working on a specific directory, only clean that.
	@if [ -n "$(DIR)" ]; then					  \
		rm -f $(DIR)/*.o $(DIR)/*-run;				  \
	else								  \
		 find $(DIRS) $(EXTRA_DIRS) -name '*.o' -o -name '*-run' | xargs rm -f; \
	fi

distclean: clean
	rm -f .depends `find . -name '*~'`

# Force it to do compile then link: override builtin rule.
% : %.c

# Eliminate "make foo out of foo.sh" rule.
% : %.sh

# You can add extra compile flags in xxx.o_ARGS.  This also includes
# current directory so #include <common/foo.h> works as expected.
%.o: %.c
	@rm -f $@
	$(COMPILE.c) $(OUTPUT_OPTION) $($@_ARGS) -I. $<

%: %.o
	@rm -f $@
	$(LINK.o) $^ $($@_ARGS) $(LOADLIBES) $(LDLIBS) -o $@

test-start:
	@echo Compiling tests...

test-end:
	@echo Tests completed.

# # Silent versions for tests compilation.
# $(CTESTS:=.o): %.o: %.c
# 	@$(COMPILE.c) $(OUTPUT_OPTION) $($@_ARGS) -I. $<

# $(CTESTS): %: %.o
# 	@$(LINK.o) $^ $($@_ARGS) $(LOADLIBES) $(LDLIBS) -o $@

# Default rule to "make" a run of a test.  Timeout if it doesn't terminate.
%-run: %
	@echo -n Running $*:
	@./run_test.sh $* $(TIMEOUT) && touch $@

# This one cleans up afterwards:
#$(CTESTS:=-run): %-run: %
#	@echo -n Running $*:; if $*; then echo YES; else echo NO; exit 1; fi
#	@rm -f $*

.PHONY: TAGS
TAGS:
	@rm -f $@
	@find $(DIRS) -name '*.h' -print0 | xargs -0 etags -o - >> TAGS
	@find $(DIRS) -name '*.c' ! -name '*_test.c' -print0 | xargs -0 etags -o - >> TAGS

# Will be made next time around.
dep:
	@rm -f .depends

# Make dependencies. gcc -MM strips paths from .c files, so hence sed fixup.
.depends:
	@echo Making dependency information...
	@rm -f $@
	@find $(DIRS) -name '*.c' |					\
		while read f; do				\
			BASE="`basename $$f .c`";		\
			$(CC) -MM $(CFLAGS) -I. "$$f" | 	\
				sed "s,^$$BASE,`dirname $$f`/$$BASE,";	\
		done > $@;

include .depends

