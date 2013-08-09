#! /usr/bin/make



# Add binaries here (each name relative to top of tree!).
# SIPL 2011: std_pref_csv is not used, so we do not build it.
#   (We would have to fix compilation warnings otherwise.)
# SIPL 2011-09-21 Removed hare_clark_csv, test_fraction.
#BINARIES+=counting/hare_clark counting/hare_clark_csv counting/std_pref_csv counting/vacancy counting/test_fraction counting/report_preferences_by_polling_place
BINARIES+=counting/hare_clark counting/vacancy counting/report_preferences_by_polling_place

# Add any extra tests to run here (each name relative to top of tree!).
EXTRATESTS+=counting/hare_clark_test.sh counting/vacancy_test.sh

# Include *_test.c automatically.
CTESTS+=$(foreach tc, $(wildcard counting/*_test.c), $(tc:.c=))

# This needs to come before any rules, so binaries is the default.
ifndef MASTER
  binaries tests clean dep TAGS:
	$(MAKE) -C .. $@ DIR="`pwd`"
endif # MASTER

counting/hare_clark: counting/count.o counting/ballot_iterators.o counting/candidate_iterators.o counting/fraction.o  common/evacs.o counting/report.o counting/fetch.o common/database.o
counting/hare_clark_ARGS:=-lpq 

counting/hare_clark_csv: counting/count.o counting/ballot_iterators.o counting/candidate_iterators.o counting/fraction.o   counting/report.o 
counting/hare_clark_csv_ARGS:= 

counting/std_pref_csv: counting/count_std_pref.o counting/ballot_iterators.o counting/candidate_iterators.o counting/fraction.o   counting/report_std_pref.o 
counting/hare_clark_csv_ARGS:= 

counting/test_fraction: counting/count.o counting/ballot_iterators.o counting/candidate_iterators.o counting/fraction.o  common/evacs.o counting/report.o counting/fetch.o common/database.o
counting/test_fraction_ARGS:=-lpq

counting/vacancy: counting/count.o counting/ballot_iterators.o counting/candidate_iterators.o counting/fraction.o  common/evacs.o counting/report.o counting/fetch.o common/database.o
counting/vacancy_ARGS:=-lpq 

counting/report_preferences_by_polling_place: counting/report_preferences_by_polling_place.o counting/report_common_routines.o common/evacs.o common/database.o
counting/report_preferences_by_polling_place_ARGS:=-lpq

counting/hare_clark_test: counting/count.o counting/ballot_iterators.o counting/candidate_iterators.o counting/fraction.o  common/evacs.o counting/report.o

counting/vacancy_test: counting/count.o counting/ballot_iterators.o counting/candidate_iterators.o counting/fraction.o  common/evacs.o counting/report.o

counting/hare_clark_VC3_test: counting/count.o counting/ballot_iterators.o counting/candidate_iterators.o counting/fraction.o  common/evacs.o counting/report.o

counting/hare_clark_VC4_test: counting/count.o counting/ballot_iterators.o counting/candidate_iterators.o counting/fraction.o  common/evacs.o counting/report.o

counting/hare_clark_VC5_test: counting/count.o counting/ballot_iterators.o counting/candidate_iterators.o counting/fraction.o  common/evacs.o counting/report.o

counting/hare_clark_VC6_test: counting/count.o counting/ballot_iterators.o counting/candidate_iterators.o counting/fraction.o  common/evacs.o counting/report.o

counting/hare_clark_test: counting/count.o

counting/report_test: common/evacs.o 

counting/hare_clark_test.sh-run: counting/hare_clark_test
