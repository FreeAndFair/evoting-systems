#! /usr/bin/make

# Add binaries here (each name relative to top of tree!).
BINARIES+=voting_server/get_rotation voting_server/authenticate voting_server/commit_vote voting_server/get_initial_cursor voting_server/display_first_preferences voting_server/set_date_time

# Add any extra tests to run here (each name relative to top of tree!).
EXTRATESTS+=voting_server/cgi_test.sh voting_server/get_rotation_test.sh

# Include *_test.c automatically.
CTESTS+=$(foreach tc, $(wildcard voting_server/*_test.c), $(tc:.c=))

# This needs to come before any rules, so binaries is the default.
ifndef MASTER
  binaries tests clean dep TAGS:
	$(MAKE) -C .. $@ DIR="`pwd`"
endif # MASTER

voting_server/cgi_test: common/http.o common/socket.o common/evacs.o 
voting_server/cgi_test.sh-run: voting_server/cgi_test
voting_server/cgi:common/evacs.o common/socket.o
voting_server/authenticate: voting_server/cgi.o voting_server/voting_server.o  common/evacs.o common/database.o common/barcode.o common/barcode_hash.o common/http.o common/socket.o  common/ballot_contents.o
voting_server/authenticate_test: voting_server/voting_server.o  common/evacs.o common/database.o common/barcode.o common/barcode_hash.o common/http.o common/socket.o common/createtables.o common/ballot_contents.o
voting_server/get_rotation: voting_server/fetch_rotation.o  common/evacs.o common/database.o common/barcode.o common/http.o common/socket.o voting_server/cgi.o
voting_server/get_rotation_test: voting_server/fetch_rotation.o  common/database.o common/barcode.o common/evacs.o common/createtables.o
voting_server/authenticate_ARGS:=-lcrypto -lpq
voting_server/authenticate_test_ARGS:=-lcrypto -lpq
voting_server/get_rotation_ARGS:=-lpq
voting_server/get_rotation_test_ARGS:=-lpq
voting_server/get_initial_cursor_ARGS:=-lpq
voting_server/display_first_preferences_ARGS:= -lcrypt -lpq
voting_server/set_date_time_ARGS:= -lcrypt -lpq

voting_server/commit_vote_test: common/http.o common/socket.o voting_server/voting_server.o common/barcode.o 
voting_server/voter: common/http.o common/socket.o voting_server/voting_server.o common/barcode.o  common/evacs.o common/database.o common/createtables.o common/barcode_hash.o
voting_server/save_and_verify_test: common/http.o common/socket.o voting_server/voting_server.o common/barcode.o  common/evacs.o common/database.o common/createtables.o common/barcode_hash.o
voting_server/multiuser_save_and_verify_test: common/http.o common/socket.o voting_server/voting_server.o common/barcode.o  common/evacs.o common/database.o common/createtables.o common/barcode_hash.o
voting_server/multiuser2_save_and_verify_test: common/http.o common/socket.o voting_server/voting_server.o common/barcode.o  common/evacs.o common/database.o common/createtables.o common/barcode_hash.o
voting_server/commit_vote_test_ARGS:=-lpq -lcrypto
voting_server/save_and_verify_test_ARGS:=-lpq -lcrypto
voting_server/voter_ARGS:=-lpq -lcrypto
voting_server/multiuser_save_and_verify_test_ARGS:=-lpq -lcrypto
voting_server/multiuser2_save_and_verify_test_ARGS:=-lpq -lcrypto
# They need this binary to run. 
voting_server/multiuser_save_and_verify_test-run: voting_server/voter
voting_server/multiuser2_save_and_verify_test-run: voting_server/voter

voting_server/reconstruct_test: common/cursor.o
voting_server/get_rotation_test_ARGS:=-lpq

voting_server/fetch_rotation_test: common/database.o  common/evacs.o common/createtables.o
voting_server/fetch_rotation_test_ARGS:=-lpq

voting_server/commit_vote: voting_server/voting_server.o voting_server/reconstruct.o voting_server/save_and_verify.o common/authenticate.o voting_server/cgi.o common/http.o common/socket.o  common/evacs.o common/barcode.o common/database.o common/cursor.o common/evacs.o common/barcode_hash.o common/ballot_contents.o

voting_server/commit_vote_ARGS:=-lpq -lcrypto

voting_server/get_rotation_test.sh-run: voting_server/get_rotation_test

voting_server/get_initial_cursor: common/database.o common/evacs.o common/http.o common/socket.o voting_server/cgi.o

voting_server/display_first_preferences: common/database.o common/evacs.o counting/fetch.o counting/ballot_iterators.o counting/candidate_iterators.o voting_server/count_first_preferences.o counting/fraction.o counting/report.o

voting_server/set_date_time: common/database.o common/evacs.o

voting_server/get_initial_cursor_test: common/database.o common/barcode.o common/evacs.o common/createtables.o

voting_server/get_initial_cursor_test_ARGS:=-lpq
