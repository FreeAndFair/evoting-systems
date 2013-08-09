#! /usr/bin/make

# Add binaries here (each name relative to top of tree!).
BINARIES+=voting_client/voting_client_bin

# SIPL 2011-06-09 Version for Targus telephone-style keypad
BINARIES+=voting_client/voting_client_targus_bin

# Add any extra tests to run here (each name relative to top of tree!).
EXTRATESTS+=voting_client/image_test.sh

# Include *_test.c automatically.
CTESTS+=$(foreach tc, $(wildcard voting_client/*_test.c), $(tc:.c=))

# This needs to come before any rules, so binaries is the default.
ifndef MASTER
  binaries tests clean dep TAGS:
	$(MAKE) -C .. $@ DIR="`pwd`"
endif # MASTER

voting_client/message_test: voting_client/image.o common/socket.o
voting_client/input_test: voting_client/input_test.o voting_client/image.o voting_client/child_barcode.o common/http.o common/socket.o voting_client/verify_barcode.o voting_client/voting_client.o common/barcode.o common/authenticate.o voting_client/message.o  common/evacs.o common/ballot_contents.o
voting_client/message_test_ARGS:=-L/usr/X11R6/lib -lX11 -lpng
voting_client/child_barcode_test_ARGS:=-L/usr/X11R6/lib -lX11
voting_client/input_test_ARGS:=-L/usr/X11R6/lib -lX11 -lpng
voting_client/image_test_ARGS:=-L/usr/X11R6/lib -lX11 -lpng
# message_test.sh needs message_test to run.
voting_client/message_test.sh-run: voting_client/message_test
voting_client/initiate_session_test: voting_client/initiate_session_test.o voting_client/message.o voting_client/image.o common/http.o common/socket.o voting_client/child_barcode.o common/authenticate.o voting_client/voting_client.o common/language.o common/ballot_contents.o
voting_client/initiate_session_test_ARGS:=-L/usr/X11R6/lib -lX11 -lpng
voting_client/verify_barcode_test: voting_client/verify_barcode_test.o voting_client/voting_client.o common/barcode.o common/authenticate.o common/http.o common/socket.o  common/evacs.o common/ballot_contents.o
voting_client/verify_barcode_test_ARGS:=-L/usr/X11R6/lib -lX11 -lpng -lcrypto
voting_client/message_integration_test: voting_client/image.o common/http.o common/socket.o
voting_client/message_integration_test_ARGS:=-L/usr/X11R6/lib -lX11 -lpng
voting_client/get_rotation_test: common/http.o common/socket.o
voting_client/main_screen_test: voting_client/main_screen_test.o common/http.o common/socket.o voting_client/message.o voting_client/image.o voting_client/audio.o voting_client/child_audio.o common/barcode.o 
voting_client/main_screen_test_ARGS:=-L/usr/X11R6/lib -lX11 -lpng -lcrypto
voting_client/start_again_test: common/http.o common/socket.o voting_client/message.o voting_client/image.o voting_client/keystroke.o voting_client/audio.o voting_client/child_audio.o 
voting_client/start_again_test_ARGS:=-L/usr/X11R6/lib -lX11 -lpng
voting_client/draw_group_entry_test: common/http.o common/socket.o voting_client/get_img_at_cursor.o voting_client/main_screen.o voting_client/message.o voting_client/image.o common/cursor.o
voting_client/draw_group_entry_test_ARGS:=-L/usr/X11R6/lib -lX11 -lpng
voting_client/move_cursor_test: common/http.o common/socket.o voting_client/draw_group_entry.o voting_client/get_img_at_cursor.o common/cursor.o voting_client/main_screen.o voting_client/message.o voting_client/image.o
voting_client/move_cursor_test_ARGS:=-L/usr/X11R6/lib -lX11 -lpng
voting_client/get_img_at_cursor_test: common/cursor.o
voting_client/undo_pref_test: common/http.o common/socket.o voting_client/message.o voting_client/image.o voting_client/move_cursor.o common/cursor.o voting_client/main_screen.o voting_client/get_img_at_cursor.o voting_client/draw_group_entry.o
voting_client/undo_pref_test_ARGS:=-L/usr/X11R6/lib -lX11 -lpng
voting_client/add_preference_test: common/http.o common/socket.o voting_client/message.o voting_client/image.o voting_client/move_cursor.o common/cursor.o voting_client/main_screen.o voting_client/get_img_at_cursor.o voting_client/draw_group_entry.o 
voting_client/add_preference_test_ARGS:=-L/usr/X11R6/lib -lX11 -lpng
voting_client/accumulate_preferences_test: common/http.o common/socket.o voting_client/message.o voting_client/image.o voting_client/draw_group_entry.o voting_client/main_screen.o voting_client/audio.o voting_client/child_audio.o voting_client/undo_pref.o voting_client/add_preference.o voting_client/move_cursor.o common/cursor.o voting_client/start_again.o voting_client/get_img_at_cursor.o 
voting_client/accumulate_preferences_test_ARGS:=-L/usr/X11R6/lib -lX11 -lpng
voting_client/confirm_vote_test: voting_client/message.o common/http.o common/socket.o voting_client/image.o
voting_client/confirm_vote_test_ARGS:=-L/usr/X11R6/lib -lX11 -lpng

voting_client/voting_client_bin: voting_client/voter_electorate.o voting_client/voting_client.o  voting_client/voter_electorate.o voting_client/initiate_session.o voting_client/accumulate_preferences.o voting_client/message.o voting_client/image.o voting_client/audio.o voting_client/child_audio.o voting_client/input.o voting_client/verify_barcode.o voting_client/main_screen.o voting_client/get_rotation.o voting_client/get_cursor.o voting_client/draw_group_entry.o voting_client/vote_in_progress.o voting_client/keystroke.o voting_client/undo_pref.o voting_client/add_preference.o voting_client/move_cursor.o voting_client/start_again.o voting_client/confirm_vote.o voting_client/commit.o voting_client/child_barcode.o common/authenticate.o voting_client/get_img_at_cursor.o common/cursor.o common/barcode.o common/http.o common/socket.o common/language.o common/ballot_contents.o common/evacs.o
voting_client/voting_client_bin_ARGS:=-L/usr/X11R6/lib -lX11 -lpng

# SIPL 2011-06-09 Version for Targus telephone-style keypad
voting_client/voting_client_targus_bin: voting_client/voting_client_bin.o voting_client/voter_electorate.o voting_client/voting_client.o  voting_client/voter_electorate.o voting_client/initiate_session.o voting_client/accumulate_preferences.o voting_client/message.o voting_client/image.o voting_client/audio.o voting_client/child_audio.o voting_client/input_targus.o voting_client/verify_barcode.o voting_client/main_screen.o voting_client/get_rotation.o voting_client/get_cursor.o voting_client/draw_group_entry.o voting_client/vote_in_progress.o voting_client/keystroke.o voting_client/undo_pref.o voting_client/add_preference.o voting_client/move_cursor.o voting_client/start_again.o voting_client/confirm_vote.o voting_client/commit.o voting_client/child_barcode.o common/authenticate.o voting_client/get_img_at_cursor.o common/cursor.o common/barcode.o common/http.o common/socket.o common/language.o common/ballot_contents.o common/evacs.o
	@rm -f $@
	$(LINK.o) $^ $($@_ARGS) $(LOADLIBES) $(LDLIBS) -o $@

voting_client/voting_client_targus_bin_ARGS:=-L/usr/X11R6/lib -lX11 -lpng

voting_client/input_targus.o: voting_client/input.c
	@rm -f $@
	$(COMPILE.c) $(OUTPUT_OPTION) $($@_ARGS) -I. voting_client/input.c

voting_client/input_targus.o_ARGS:=-DTARGUS_KEYPAD

voting_client/child_audio_test: common/evacs.o 
voting_client/audio_test: voting_client/child_audio.o common/http.o common/socket.o common/evacs.o 
