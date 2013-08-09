/* This file is (C) copyright 2001 Software Improvements, Pty Ltd */

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
#include <pwd.h>
#include <stdarg.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <string.h>
#include <time.h>
#include <unistd.h>
#include <fcntl.h>
#include <stdlib.h>
#include "evacs.h"
/*#include "safe.h"*/

/* Place any globals here */

/* DDS???: Get Operator ID */
extern char *get_operator_id(void)
{
	char *name;

	struct passwd *passwd;
	
	passwd = getpwuid(getuid());
	
	name = malloc(strlen(passwd->pw_name) * sizeof(char) + 1);
	
	strcpy(name, passwd->pw_name);

	name[8] = '\0';
	
	return name;
}

/* Default bailout function is "bailout" from evacs.c */
static void (*bailoutfn)(const char *fmt, va_list ap) __attribute__((noreturn))
= NULL;

void set_bailout(void (*bailoutfunc)(const char *fmt, va_list ap)
		 __attribute__((noreturn)))
{
	bailoutfn = bailoutfunc;
}

void bailout(const char *fmt, ...)
     /*
       Print a message and exit fatally.
     */
{
  va_list arglist;

  va_start(arglist,fmt);
  if (bailoutfn) {
	  /* Use their handler */
	  bailoutfn(fmt, arglist);
  } else {
	  /* Default handler */
	  fprintf(stderr,"FATAL: ");
	  vfprintf(stderr,fmt,arglist);
  }
  va_end(arglist);
  
  exit(1);
}

void create_directory(mode_t mode,const char *fmt, ...)
     /*
       This function creates a directory but accepts the parameters
       of both mkdir_safe and sprintf_malloc, with mode_t at the start.

       The sprintf constructs the dir_name, using sprintf_malloc.
       The directory is then created using mkdir_safe and the buf
       returned to the free pool with free_safe.
      */
{
  char *buf;
  va_list arglist;

  va_start(arglist,fmt);
  buf = vsprintf_malloc(fmt,arglist);
  va_end(arglist);

  mkdir(buf,mode);

  free(buf);
}

void copy_file(const char *source_file,const char *target_file)
     /*
       Copy file from source to target.
     */
{
  struct stat file_stat;
  int source_fd,target_fd;
  void *file_contents;

  /* Open files */

  source_fd = open(source_file,O_RDONLY,0); /* 3rd parm for _open_safe macro */
  target_fd = open(target_file,O_CREAT|O_WRONLY,S_IRWXU);

  /* Get size of source file */

  fstat(source_fd,&file_stat);

  /* Allocate memory for entire file */

  file_contents = malloc(file_stat.st_size);

  /* Copy the file */
  /* DDS3.2: Get Electorate Image */
  /* DDS3.2: Get Preference Number Data */
  read(source_fd,file_contents,file_stat.st_size);
  write(target_fd,file_contents,file_stat.st_size);

  /* Cleanup */

  close(source_fd);
  close(target_fd);
  free(file_contents);
}

static int strip_nl(char *s)
     /*
       Return true (1) if string s contained a trailing newline. The
       string s will be returned minus this character.

       Otherwise return false (0), string s is untouched.
     */
{
  int len=strlen(s)-1;

  if (len >= 0 && s[len] == '\n') {
    s[len] = '\0';
    return(1);
  }
  else
    return(0);
}

/*
	sprintf_malloc and fgets_malloc perform a similar function
	to calling malloc and sprintf and malloc and fgets respectively.

	Each function allocates the memory it needs to perform its
	operation. They return a pointer to the newly allocated
	memory.

	These functions have the word malloc in them to remind the 
	programmer that they allocate storage that must therefore
	be freed at some time.

	free_safe() MUST be used to free the pointers returned by these
	functions since malloc_safe() was used to allocate the storage.
	Failure to do so may cause a "memory leak" bailout before
	returning from the top-level function.
*/
     
char *vsprintf_malloc(const char *fmt, va_list arglist)
     /*
       This is a self-allocating vsprintf function.
       
       NOTE: This function allocates memory. It is
       the callers responsibility to free it after
       use. Also, this function does not call va_end.
       It is the callers responsibility to do this.
      */

{
  char *str=NULL;

  /* Allocate amount of space indicated by vsnprintf */

  str = (char *)malloc(vsnprintf(str,0,fmt,arglist)+1);

  /* Write into string for real this time */

  vsprintf(str,fmt,arglist);
  return(str);
}

char *sprintf_malloc(const char *fmt, ...)
     /*
       Variable number of parameter interface to vsprintf_malloc().
     */
     
{
  char *str;
  va_list arglist;
  
  va_start(arglist,fmt);
  str = vsprintf_malloc(fmt,arglist);
  va_end(arglist);
  
  return(str);
}

char *fgets_malloc(FILE *stream)
     /*
       Returns a pointer to the next line of text read from
       the stream.

       NOTE: This function allocates memory if end of file
       was not encountered and no characters were copied to
       the string. It is the callers responsibility
       to free it after use. If end of file was encountered
       then the memory is released before return.
     */
{ 
  char *str;
  int start=0,empty_size,size=128;
  
  str = malloc(size);
  *str = '\0';
  empty_size = size;
  
  /* Loop until newline or EOF encountered */

  while (1) {
    if ( fgets(&str[start],empty_size,stream) == NULL ) { /* end-of-file ? */
      if ( *str == '\0' ) {  /* and nothing in the buffer */
	free(str);
	return(NULL);  /* then return NULL*/
      }
      else {
	strip_nl(str);
	break;   /* otherwise return string */
      }
    }
    
    if (strip_nl(str))  /* If string contained a newline at the end */
      break;      /* then return it */

    /* Newline not hit - double buf size and read some more */

    start += size-1;    
    empty_size = size+1;  /* We score one extra byte due to null terminator */
    size *= 2;
    str = realloc(str,size);
  }
  
  return(str);
}

extern struct preference_set *unpack_preferences(const char *preference_list)
{
	struct preference_set *vote;
	char *pref_ptr;   
	unsigned int num_preferences=0,i;
	unsigned int pref_number, group_index, db_cand_index;

	for (pref_ptr=(char *)preference_list;
	     strlen(pref_ptr)>=DIGITS_PER_PREF;
	     pref_ptr += DIGITS_PER_PREF*sizeof(char),num_preferences++);
	
	if ( strlen(pref_ptr)) 
		bailout("Malformed preference list: '%s'\n",preference_list);
	
	vote = malloc(sizeof(*vote)
			+ sizeof(vote->candidates[0]) * num_preferences);
	vote->num_preferences = num_preferences;
	
	/* They may not be in order */
	for (pref_ptr=(char *)preference_list, i = 0;
	     i < vote->num_preferences; 
	     i++,pref_ptr += DIGITS_PER_PREF*sizeof(char) )
	{
		sscanf(pref_ptr,"%2u%2u%2u",&pref_number,&group_index,&db_cand_index);
		
		vote->candidates[i]
			.group_index = group_index;
		vote->candidates[i]
			.db_candidate_index = db_cand_index;
		vote->candidates[i]
			.prefnum = pref_number;
	}
	
	return vote;
	
}


char *preference_string(struct preference_set *vote)
{
	unsigned int i;
	/* SIPL 2011-09-26 Increase array size by one to allow
	   space for null at end, to cope with the case where there
	   really are PREFNUM_MAX preferences in the vote. */
	char pref_string[PREFNUM_MAX * DIGITS_PER_PREF + 1];
	char *return_string, *pref_ptr, *p;
	
	pref_string[0]='\0';
	for (i=0; i <  vote->num_preferences; i++) {
		/* accumulate new preference */
		p = sprintf_malloc("%02u%02u%02u",vote->candidates[i].prefnum,
				   vote->candidates[i].group_index,
				   vote->candidates[i].db_candidate_index);
		pref_ptr=&pref_string[0]+sizeof(char)*((i)*DIGITS_PER_PREF);
		strcpy(pref_ptr,p);
		free(p);
	}
	return_string=malloc(sizeof(char) * (strlen(pref_string) + 1));
	strcpy(return_string,pref_string);
	
	return return_string;

}

char *generate_timestamp(void)
{
	time_t systime = time(NULL);
	char  *timestamp = malloc(strlen(ctime(&systime)+3));
	
	strcpy(timestamp,ctime(&systime));
	strip_nl(timestamp);
	
	return timestamp;
}

extern char *generate_sortable_timestamp(void) 
{
       
	time_t systime=time(NULL);
	struct tm *time=localtime(&systime);

	char *timestamp=sprintf_malloc("%4i-%02i-%02i %02i:%02i:%02i",
				      time->tm_year+1900,
				       /* SIPL 2011-08-19 Next line was
					"time->tm_mon".  But tm_mon is
					indexed from 0. */
				      time->tm_mon+1,
				      time->tm_mday,
				      time->tm_hour,
				      time->tm_min,
				      time->tm_sec
		);

	return timestamp;
}

char *get_batch_number_string(const int elec,
			      const int pp)
{
 return sprintf_malloc("%u%03u000",elec,pp);
}
