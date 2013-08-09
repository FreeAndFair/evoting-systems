#! /usr/bin/make

# Add binaries here (each name relative to top of tree!).
BINARIES+=data_entry/batch_entry_bin

# Add any extra tests to run here (each name relative to top of tree!).
EXTRATESTS+=

# Include *_test.c automatically.
CTESTS+=$(foreach tc, $(wildcard data_entry/*_test.c), $(tc:.c=))

# This needs to come before any rules, so binaries is the default.
ifndef MASTER
  binaries tests clean dep TAGS:
	$(MAKE) -C .. $@ DIR="`pwd`"
endif # MASTER

# SIPL 2011-06-08 use "customized" message.o.
data_entry/batch_entry_bin: data_entry/batch_entry.o data_entry/accumulate_deo_preferences.o  data_entry/interpret_deo_keystroke.o data_entry/confirm_paper.o data_entry/get_paper_version.o data_entry/handle_end_batch_screen.o data_entry/delete_deo_preference.o  data_entry/update_deo_preference.o data_correction/batch_edit.o  data_correction/batch_edit_2.o data_entry/voter_electorate.o common/current_paper_index.o common/ballot_contents.o common/get_electorate_ballot_contents.o  common/database.o common/batch.o common/evacs.o common/find_errors.o common/language.o  common/http.o common/socket.o common/cursor.o  common/batch_history.o voting_client/image.o data_entry/message.o voting_client/main_screen.o voting_client/get_rotation.o  data_entry/move_deo_cursor.o voting_client/vote_in_progress.o common/cursor.o   voting_client/draw_group_entry.o voting_client/get_img_at_cursor.o voting_server/fetch_rotation.o voting_client/get_rotation.o data_entry/prompts.o data_entry/enter_paper.o data_entry/dummy_audio.o election_night/update_ens_summaries.o

data_entry/batch_entry_bin_ARGS:=-lpq -L/usr/X11R6/lib -lpng -lX11

# SIPL 2011-06-08 Compile message.c based on data-entry-specific images.
#  Use the existing dependencies of voting_client/message.o.
data_entry/message.o: voting_client/message.o
	@rm -f $@
	$(COMPILE.c) $(OUTPUT_OPTION) $($@_ARGS) -I. voting_client/message.c

data_entry/message.o_ARGS:=\
  -DDATA_ENTRY \
  -D'IMAGE_BASE="/images.1152/messages/"' \
  -D'NUMBER_BASE="/images.1152/%u/numbers/"' \
  -D'CANDIDATE_BASE="/images.1152/electorates/"' \
  -D'GROUP_BASE="/images.1152/electorates/"'

data_entry/batch_entry_test: data_entry/batch_entry.o  common/createtables.o data_entry/accumulate_deo_preferences.o  data_entry/interpret_deo_keystroke.o data_entry/confirm_paper.o data_entry/get_paper_version.o data_entry/handle_end_batch_screen.o data_entry/update_deo_preference.o  data_entry/delete_deo_preference.o data_entry/update_deo_preference.o data_entry/delete_deo_preference.o data_correction/batch_edit.o  data_correction/batch_edit_2.o data_entry/voter_electorate.o common/current_paper_index.o common/ballot_contents.o common/get_electorate_ballot_contents.o  common/database.o common/batch.o common/evacs.o common/find_errors.o common/language.o  common/http.o common/socket.o common/cursor.o  voting_client/image.o voting_client/message.o voting_client/main_screen.o voting_client/get_rotation.o  data_entry/move_deo_cursor.o voting_client/vote_in_progress.o common/cursor.o   voting_client/draw_group_entry.o voting_client/get_img_at_cursor.o voting_server/fetch_rotation.o voting_client/get_rotation.o data_entry/prompts.o data_entry/enter_paper.o data_entry/dummy_audio.o election_night/update_ens_summaries.o


data_entry/batch_entry_test_ARGS=-lpq -L/usr/X11R6/lib -lpng -lX11 

data_entry/confirm_paper: common/find_errors.o  common/current_paper_index.o 

data_entry/confirm_paper_test:  common/database.o common/find_errors.o  common/current_paper_index.o
data_entry/confirm_paper_test_ARGS:=-lpq 

data_entry/build_tables_test: data_entry/build_tables_test.o common/database.o common/batch.o common/evacs.o  common/createtables.o
data_entry/build_tables_test_ARGS:=-lpq

data_entry/move_deo_cursor_test: common/http.o common/socket.o voting_client/move_cursor.o voting_client/draw_group_entry.o voting_client/message.o voting_client/image.o voting_client/main_screen.o voting_client/get_img_at_cursor.o common/cursor.o data_entry/dummy_audio.o
data_entry/move_deo_cursor_test_ARGS:=-L/usr/X11R6/lib -lX11 -lpng
data_entry/get_paper_version_test: common/http.o common/socket.o voting_client/move_cursor.o voting_client/draw_group_entry.o voting_client/message.o voting_client/image.o voting_client/main_screen.o voting_client/get_img_at_cursor.o common/cursor.o common/database.o  common/evacs.o voting_server/fetch_rotation.o common/ballot_contents.o common/language.o voting_client/input.o voting_client/vote_in_progress.o voting_client/get_rotation.o voting_client/child_barcode.o data_entry/dummy_audio.o
data_entry/get_paper_version_test_ARGS:=-L/usr/X11R6/lib -lX11 -lpng -lpq
data_entry/update_deo_preference_test: common/http.o common/socket.o common/cursor.o voting_client/draw_group_entry.o voting_client/image.o voting_client/message.o voting_client/main_screen.o voting_client/get_img_at_cursor.o voting_client/vote_in_progress.o data_entry/dummy_audio.o 
data_entry/update_deo_preference_test_ARGS:=-L/usr/X11R6/lib -lX11 -lpng
data_entry/delete_deo_preference_test: common/http.o common/socket.o common/cursor.o voting_client/draw_group_entry.o voting_client/image.o voting_client/message.o voting_client/main_screen.o voting_client/get_img_at_cursor.o voting_client/vote_in_progress.o data_entry/update_deo_preference.o data_entry/dummy_audio.o data_entry/dummy_audio.o
data_entry/delete_deo_preference_test_ARGS:=-L/usr/X11R6/lib -lX11 -lpng
data_entry/accumulate_deo_preferences_test: common/http.o common/socket.o voting_client/image.o voting_client/message.o voting_client/main_screen.o data_entry/move_deo_cursor.o voting_client/vote_in_progress.o data_entry/update_deo_preference.o data_entry/delete_deo_preference.o common/cursor.o voting_client/draw_group_entry.o voting_client/get_img_at_cursor.o data_entry/prompts.o data_entry/dummy_audio.o
data_entry/accumulate_deo_preferences_test_ARGS:=-L/usr/X11R6/lib -lX11 -lpng
data_entry/confirm_paper_test: common/find_errors.o  common/current_paper_index.o common/current_paper_index.o

data_entry/handle_end_batch_screen_test: common/evacs.o 
data_entry/handle_end_batch_screen_test_ARGS:=-L/usr/X11R6/lib -lX11 -lpng

data_entry/enter_paper_test:  data_entry/batch_entry.o  common/createtables.o data_entry/accumulate_deo_preferences.o  data_entry/interpret_deo_keystroke.o data_entry/confirm_paper.o data_entry/get_paper_version.o data_entry/handle_end_batch_screen.o data_entry/update_deo_preference.o  data_entry/delete_deo_preference.o data_entry/update_deo_preference.o data_entry/delete_deo_preference.o data_correction/batch_edit.o  data_correction/batch_edit_2.o data_entry/voter_electorate.o common/current_paper_index.o common/ballot_contents.o common/get_electorate_ballot_contents.o  common/database.o common/batch.o common/evacs.o common/find_errors.o common/language.o  common/http.o common/socket.o common/cursor.o  voting_client/image.o voting_client/message.o voting_client/main_screen.o voting_client/get_rotation.o  data_entry/move_deo_cursor.o voting_client/vote_in_progress.o common/cursor.o   voting_client/draw_group_entry.o voting_client/get_img_at_cursor.o voting_server/fetch_rotation.o voting_client/get_rotation.o data_entry/prompts.o data_entry/enter_paper.o data_entry/dummy_audio.o common/current_paper_index.o

data_entry/enter_paper_test_ARGS = -lpq -L/usr/X11R6/lib -lX11 -lpng
