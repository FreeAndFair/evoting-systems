#ifndef _SAFE_H
#define _SAFE_H
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

/* This file contains wrappers for common functions, and calls
   bailout() on failure. */
#include <stdio.h>
#include <stdbool.h>
#include <sys/types.h>
#include <dirent.h>

#define open(pathname,flags,mode) _open_safe(pathname,flags,mode, __FILE__,__LINE__)
#define close(fd) _close_safe(fd,__FILE__,__LINE__)
#define write(fd,buf,count) _write_safe(fd,buf,count,__FILE__,__LINE__)
#define fstat(fd,buf) _fstat_safe(fd,buf, __FILE__,__LINE__)
#define stat(filename,buf) _stat_safe(filename,buf,__FILE__,__LINE__)
#define fopen(filename,mode) _fopen_safe(filename,mode,__FILE__,__LINE__)
#define fclose(fp) _fclose_safe(fp,__FILE__,__LINE__)
#define opendir(name) _opendir_safe(name,__FILE__,__LINE__)
#define closedir(dir) _closedir_safe(dir,__FILE__,__LINE__)
#define mkdir(pathname,mode) _mkdir_safe(pathname,mode,__FILE__,__LINE__)
#define malloc(size) _malloc_safe(size,__FILE__,__LINE__)
#define realloc(ptr,size) _realloc_safe(ptr,size,__FILE__,__LINE__)
#define free(ptr) _free_safe(ptr,__FILE__,__LINE__)
/* Strdup is a #define already on some platforms 8( */
#undef strdup
#define strdup(string) _strdup_safe(string,__FILE__,__LINE__)

/* By default, our read insists on getting everything we ask for... */
#define read(fd,buf,count) _read_safe(fd,buf,count,false,__FILE__,__LINE__)
/* So we define read_short which can return short */
#define read_short(fd,buf,count) _read_safe(fd,buf,count,true,__FILE__,__LINE__)

/* Check to assert that all memory has been freed */
#define check_for_memory_leak() _check_for_memory_leak(__FUNCTION__)

struct stat;

extern void _check_for_memory_leak(const char *function_name);
extern int _open_safe(const char *filename, int flags,mode_t mode,
		      const char *file,unsigned int line);
extern int _close_safe(int fd,const char *file,unsigned int line);
extern ssize_t _read_safe(int fd,void *buf,size_t count,bool short_ok,
			  const char *file,unsigned int line);
extern ssize_t _write_safe(int fd,const void *buf,size_t count,
			   const char *file,unsigned int line);
extern int _fstat_safe(int fd,struct stat *buf,const char *file,
		       unsigned int line);
extern int _stat_safe(const char *filename,struct stat *buf,
		      const char *file,unsigned int line);
extern FILE *_fopen_safe(const char *filename,const char *mode,
			 const char *file,unsigned int line);
extern int _fclose_safe(FILE *fp,const char *file,unsigned int line);
extern DIR *_opendir_safe(const char *name,const char *file,unsigned int line);
extern int _closedir_safe(DIR *dir,const char *file,unsigned int line);
extern int _mkdir_safe(const char *pathname,mode_t mode,
		       const char *file,unsigned int line);
extern void *_malloc_safe(size_t size,const char *file,unsigned int line);
extern char *_strdup_safe(const char *str,const char *file,unsigned int line);
extern void *_realloc_safe(void *ptr,size_t size,
			   const char *file,unsigned int line);
extern void _free_safe(void *ptr,const char *file,unsigned int line);

#endif /*_SAFE_H*/
