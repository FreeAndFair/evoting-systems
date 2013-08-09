/* This file is (C) copyright 2011 Software Improvements, Pty Ltd */

/* This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 2 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA. */

/* This program prompts the user for a password, and, if it is correct,
   allows the user to set the date/time. */
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <ctype.h>
#include <crypt.h>
#include <sys/types.h>
#include <regex.h>
#include <unistd.h>
#include <termios.h>
#include <common/database.h>
#include <common/evacs.h>

#define PASSWORD_LENGTH 8
#define HASH_LENGTH 13

/* Fedora hard-codes this uid, so we do too. */
#define POSTGRES_UID 26

/* Enough for "YYYY-MM-DD HH:MM:SS" */
#define DATE_TIME_REGEX "[0-9][0-9][0-9][0-9]-[0-9][0-9]-[0-9][0-9] " \
  "[0-9][0-9]:[0-9][0-9]:[0-9][0-9]"

#define DATE_TIME_LENGTH 25
#define DATE_COMMAND "/bin/date -s \"%s\""
/* Maximum length of the date command; subtract 2 for %s.
   Note: this calculation includes space for null. */
#define DATE_COMMAND_LENGTH (sizeof(DATE_COMMAND) - 2 + DATE_TIME_LENGTH)


// Prompts the user for a password, returns a hash of the password using crypt
static char *prompt_for_password()
{
  char password[PASSWORD_LENGTH + 1];
  char *password_encrypted;
  int i;
  char c = 0;

  password_encrypted = malloc(sizeof(char)*(HASH_LENGTH + 1));

  /* Disable echo. */
  /* oflags stores the current tty state;
     nflags stores oflags, but with ECHO disabled and ECHONL enabled. */
  struct termios oflags, nflags;

  /* First parameter to tcgetattr() and tcsetattr() is 0 (i.e.,
     standard input). */
  tcgetattr(0, &oflags);
  nflags = oflags;
  nflags.c_lflag &= ~ECHO;
  nflags.c_lflag |= ECHONL;
  
  if (tcsetattr(0, TCSANOW, &nflags) != 0) {
    perror("tcsetattr");
    return NULL;
  }
  
  fprintf(stderr, "Please enter the password: ");
    // Read up to 8 characters into password
  for(i=0; i<PASSWORD_LENGTH && (c = getchar()) != '\n'; i++) {
    password[i] = c;
  }
  // Append null.
  password[i] = '\0';
  // Discard the rest of the line.
  for (;c != '\n'; c = getchar()) {}
  
  /* Restore terminal state. */
  if (tcsetattr(0, TCSANOW, &oflags) != 0) {
    perror("tcsetattr");
    return NULL;
  }

  // Encrypt the password, the extra security from implementing a random salt
  // is not needed here.
  strcpy(password_encrypted, crypt(password, "eV"));
  if (password_encrypted == NULL) {
    printf("Encryption failed");
    return NULL;
  }
  password_encrypted[HASH_LENGTH] = '\0';

  // Erase the plaintext password from memory
  for(i=0; i<PASSWORD_LENGTH + 1; i++) {
    password[i] = '\0';
  }

  return password_encrypted;
}

static int set_date_time(void)
{
  /* Space for null not already included. */
  char date_time[DATE_TIME_LENGTH + 1];
  /* Space for null already included. */
  char date_command[DATE_COMMAND_LENGTH];
  int i;
  char c = 0;

  regex_t preg;
  int regex_return;

  int exit_code;

  fprintf(stderr, "Enter new date and time (format: YYYY-MM-DD HH:MM:SS): ");

  // Read characters into date_time
  i = 0;
  c = getchar();
  while (i<DATE_TIME_LENGTH && (c != '\n')) {
    if (isdigit(c) || (c == '-') || (c == ' ') || (c == ':')) {
      date_time[i] = c;
      i++;
    } else {
      printf("Skipping invalid character: %c\n", c);
    }
    c = getchar();
  }

  /* Append with null */
  date_time[i] = '\0';
  /* Discard rest of line */
  for (;c != '\n'; c = getchar()) {}

  /* Check validity. */
  regex_return = regcomp(&preg, DATE_TIME_REGEX, 0);
  if (regex_return != 0) {
    fprintf(stderr, "Error compiling regular expression.\n");
    return -1;
  }

  regex_return = regexec(&preg, date_time, 0, 0, 0);
  if (regex_return != 0) {
    fprintf(stderr, "Invalid date/time format.\n"
	    "The correct format is: YYYY-MM-DD HH:MM:SS\n");
    return -1;
  }

  sprintf(date_command, DATE_COMMAND, date_time);
  exit_code = system(date_command);

  if (exit_code != 0) {
    fprintf(stderr, "Setting the date/time failed.\n"
	    "Perhaps you used the wrong format.\n"
	    "The correct format is: YYYY-MM-DD HH:MM:SS\n");
  }

  return exit_code;
}

//int main(int argc, char *argv[])
int main()
{
  PGconn *conn;
  char *password_hash;
  char *valid_password_hash;
  
  /* Connect to the database */
  /* Necessary first to become the postgres user. */
  seteuid(POSTGRES_UID);
  conn = connect_db(DATABASE_NAME);
  if (conn == NULL) bailout("Can't connect to database:%s\n",
			    DATABASE_NAME);
  valid_password_hash= SQL_singleton(conn,
		     "SELECT password_hash_date_time FROM master_data;");
  PQfinish(conn);

  /* Done, now become root again. */
  seteuid(0);
  
  /* Get the password from the user, and compare to password in database */
  password_hash = prompt_for_password();
    fprintf(stderr, "\n");
  if( strcmp(password_hash, valid_password_hash) ) {
    fprintf(stderr, "Invalid password.\n");
    free(password_hash);
    free(valid_password_hash);
    return(-1);
  }
  free(password_hash);
  free(valid_password_hash);

  /* Password was OK; now set the date and time. */
  return set_date_time();
}
