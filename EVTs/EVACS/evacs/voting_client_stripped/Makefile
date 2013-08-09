#! /usr/bin/make

# Add binaries here (each name relative to top of tree!).
BINARIES+=voting_client_stripped/voting_client_stripped_bin

# Add any extra tests to run here (each name relative to top of tree!).
EXTRATESTS+=

# Include *_test.c automatically.
CTESTS+=$(foreach tc, $(wildcard voting_client_stripped/*_test.c), $(tc:.c=))

# This needs to come before any rules, so binaries is the default.
ifndef MASTER
  binaries tests clean dep TAGS:
	$(MAKE) -C .. $@ DIR="`pwd`"
endif # MASTER

voting_client_stripped/voting_client_stripped_bin: voting_client_stripped/voting_client.o  voting_client_stripped/voter_electorate.o voting_client_stripped/initiate_session.o voting_client_stripped/accumulate_preferences.o voting_client_stripped/message.o voting_client_stripped/image.o voting_client_stripped/main_screen.o voting_client_stripped/get_rotation.o voting_client_stripped/draw_group_entry.o voting_client_stripped/vote_in_progress.o common/authenticate.o voting_client_stripped/get_img_at_cursor.o common/http.o common/cursor.o common/socket.o common/language.o common/ballot_contents.o common/database.o common/evacs.o

voting_client_stripped/voting_client_stripped_bin_ARGS:=-L/usr/X11R6/lib -lX11 -lpng -lpq
