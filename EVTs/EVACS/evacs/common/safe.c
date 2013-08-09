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
#include <assert.h>
#include <string.h>
#include <stdio.h>
#include <limits.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <errno.h>
#include <fcntl.h>
#include <dirent.h>
#include <unistd.h>
#include <stdarg.h>
#include <stdlib.h>
#include <libpq-fe.h> 
#include "evacs.h"
#include "safe.h"

struct allocated {
  void *ptr;
  struct allocated *next;
};

/* Place any globals here */
static struct allocated *head_ptr=NULL;

/*
  _xyz_safe functions.

  These functions are wrappers for function xyz. If the function returns
  and error then bailout is called with strerror(errno), where appropriate.
  
  Each function has an associated #define function which calls it whenever the
  'real' function is used.
  
  e.g. #define open(pathname,flags,mode) _open_safe(pathname,flags,mode,
  __FILE__, __LINE__)
  
*/

/* We need to undefine these, but we want the prototypes from safe.h */
#undef open
#undef close
#undef read
#undef write
#undef fstat
#undef stat
#undef fopen
#undef fclose
#undef opendir
#undef closedir
#undef mkdir
#undef malloc
#undef strdup
#undef realloc
#undef free

int _open_safe(const char *filename, int flags,mode_t mode,
	       const char *file,unsigned int line)
     /*
       Try to open file. Bailout on error.
     */
{
  int fd;
  
  if (mode)
    fd = open(filename,flags,mode);
  else
    fd = open(filename,flags);
  
  if (fd == -1)
    bailout("Cannot open file %s\n%s (%s at line %u)\n",
	    filename,strerror(errno),file,line);
  
  return(fd);
}

int _close_safe(int fd,const char *file,unsigned int line)
     /*
       Try to close file. Bailout on error.
     */
{
  int ret;
  
  if ((ret = close(fd)) != 0)
    bailout("Close failed on file.\n%s (%s at line %u)\n",
	    strerror(errno),file,line);
  
  return(ret);
}

ssize_t _read_safe(int fd,void *buf,size_t count, bool short_ok,
		   const char *file,unsigned int line)
     /*
       Read from file, bailout if error occurs.
     */
{
  ssize_t bytes;
  size_t todo, done;

  todo = count;
  done = 0;
  while (todo > 0) {
	  bytes = read(fd, buf+done, todo);
	  if (short_ok && bytes == 0) break;
	  if (bytes <= 0) 
		  bailout("read of %d bytes of %u from file failed.\n"
			  "%s (%s at line %u)\n",
			  todo, count, strerror(errno), file, line);
	  done += bytes;
	  todo -=bytes;
  }

  return (done);
}

ssize_t _write_safe(int fd,const void *buf,size_t count,
		    const char *file,unsigned int line)
     /*
       Write to file, bailout if error occurs.
     */
{
  ssize_t bytes;
  size_t todo, done;

  todo = count;
  done = 0;
  while (todo > 0) {
	  bytes = write(fd, buf+done, todo);
	  if (bytes <= 0) 
		  bailout("Write of %d bytes to file failed.\n"
			  "%s (%s at line %u)\n",
			  count, strerror(errno), file, line);
	  done += bytes;
	  todo -=bytes;
  }

  return(done);
}

int _fstat_safe(int fd,struct stat *buf,const char *file,unsigned int line)
     /*
       Get information about open file. Bailout on error.
     */
{
  int ret;

  if ((ret = fstat(fd,buf)) != 0) {
    close(fd); /* Attempt to close it first */
    bailout("Cannot get information about open file.\n%s (%s at line %u)\n",
	    strerror(errno),file,line);
  }
  return(ret);
}

int _stat_safe(const char *filename,struct stat *buf,
	       const char *file,unsigned int line)
     /*
       Get information about file. Bailout on error.
     */
{
  int ret;

    if ((ret = stat(filename,buf)) != 0)
      bailout("Cannot get information about file %s\n%s (%s at line %u)",
	      filename,strerror(errno),file,line);
    return(ret);
}

FILE *_fopen_safe(const char *filename,const char *mode,
		  const char *file,unsigned int line)
     /*
       Try to fopen file. Bailout on error.
     */
{
  FILE *fp;

  if ((fp = fopen(filename,mode)) == NULL)
      bailout("File open failed on %s\n%s (%s at line %u)\n",
	      filename,strerror(errno),file,line);

  return(fp);
}

int _fclose_safe(FILE *fp,const char *file,unsigned int line)
     /*
       Try to fclose file. Bailout on error.
     */
{
  int ret;

  if ((ret = fclose(fp)) != 0)
    bailout("Close file failed.\n%s (%s at line %u)\n",
	    strerror(errno),file,line);

  return(ret);
}

DIR *_opendir_safe(const char *name,const char *file,unsigned int line)
     /*
       Open the directory. Bailout on failure.
     */
{
  DIR *dir;

  if ((dir = opendir(name)) == NULL)
    bailout("Cannot open directory %s\n%s (%s at line %u)\n",
	    name,strerror(errno),file,line);

  return(dir);
}

int _closedir_safe(DIR *dir,const char *file,unsigned int line)
     /*
       Close the directory. Bailout on failure.
     */
{
  int ret;

  if ((ret = closedir(dir)) != 0) 
    bailout("Cannot close directory \n%s (%s at line %u)\n",strerror(errno),file,line);

  return(ret);
}

int _mkdir_safe(const char *pathname,mode_t mode,
		const char *file,unsigned int line)
     /*
       Make a directory. Bailout on failure.
     */
{
  int ret;

  if ((ret = mkdir(pathname,mode)) != 0)
    bailout("Cannot create directory %s\n%s (%s at line %u)\n",
	    pathname,strerror(errno),file,line);

  return(ret);
}

void *_malloc_safe(size_t size,const char *file,unsigned int line)
     /*
       Try to malloc memory. Bailout on failure.
     */
{
  struct allocated *mem_ptr;

  /* Add pointer to list of allocated memory areas */

  if ((mem_ptr = malloc(sizeof(struct allocated))) == NULL ||
      (mem_ptr->ptr = malloc(size)) == NULL)
      bailout("Cannot allocate %d bytes of memory.\n%s (%s at line %u)\n",
	      size,strerror(errno),file,line);

  mem_ptr->next = head_ptr;
  head_ptr = mem_ptr;

  return(mem_ptr->ptr);
}

/* Must not use strdup here!  On some platforms, it is a macro */
char *_strdup_safe(const char *str,const char *file,unsigned int line)
{
	char *ret;

	ret = _malloc_safe(strlen(str)+1, file, line);
	strcpy(ret, str);
	return ret;
}

void *_realloc_safe(void *ptr,size_t size,const char *file,unsigned int line)
     /*
       Try to realloc_safe memory. Bailout on failure.
     */
{
  void *new_ptr;
  struct allocated *mem_ptr;

  if ( (new_ptr = realloc(ptr,size)) == NULL)
      bailout("Cannot re-allocate %d bytes of memory.\n%s (%s at line %u)\n",
	      size,strerror(errno),file,line);

  for (mem_ptr=head_ptr;mem_ptr;mem_ptr=mem_ptr->next) {
    if (mem_ptr->ptr == ptr) {
      mem_ptr->ptr = new_ptr; /* Replace old ptr with new one */
      return new_ptr;
    }
  }    
  /* ptr was not found in the list - bail */
  bailout("Reallocate failed.\nCannot find pointer in list."
	  "(%s at line %u)\n",file,line);
}

void _free_safe(void *ptr,const char *file,unsigned int line)
     /*
       Free the memory pointed to by ptr.
       Remove ptr from allocated list if found.
       If it is not in the allocated list, then bail!
     */
{
  struct allocated **mem_ptr;

  /* Find the pointer in the allocated memory list */

  for (mem_ptr=&head_ptr; *mem_ptr; mem_ptr=&(*mem_ptr)->next)
    if ((*mem_ptr)->ptr == ptr) {
      struct allocated *delete = *mem_ptr;
      /* unlink from the list */
      *mem_ptr = (*mem_ptr)->next;

      free(delete);  /* Free list item */
      free(ptr); /* and the memory it pointed to */

      return;
    }

  /* If we got here then the ptr was not found in the list - bail! */

  bailout("free_safe failed.\n"
	  "Not found in allocated list. (%s at line %u)\n",file,line);
}

void _check_for_memory_leak(const char *function_name)
     /*
       Call this before returning from an exposed function.

       This checks that head_ptr is NULL. If it is not then
       some memory has been alloced by malloc_safe but 
       not freed with free_safe.

       This does not necessarily indicate a logic error. It
       might simply mean that free() was used instead of
       free_safe() to free a block of memory.
     */
{
  if (head_ptr != NULL)
    bailout("Possible memory leak detected in %s.\n",function_name);
}
