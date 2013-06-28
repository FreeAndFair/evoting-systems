/*  */
/* This material is subject to the VoteHere Source Code Evaluation */
/* License Agreement ("Agreement").  Possession and/or use of this */
/* material indicates your acceptance of this Agreement in its entirety. */
/* Copies of the Agreement may be found at www.votehere.net. */
/*  */
/* Copyright 2004 VoteHere, Inc.  All Rights Reserved */
/*  */
/* You may not download this Software if you are located in any country */
/* (or are a national of a country) subject to a general U.S. or */
/* U.N. embargo or are deemed to be a terrorist country (i.e., Cuba, */
/* Iran, Iraq, Libya, North Korea, Sudan and Syria) by the United States */
/* (each a "Prohibited Country") or are otherwise denied export */
/* privileges from the United States or Canada ("Denied Person"). */
/* Further, you may not transfer or re-export the Software to any such */
/* country or Denied Person without a license or authorization from the */
/* U.S. government.  By downloading the Software, you represent and */
/* warrant that you are not a Denied Person, are not located in or a */
/* national of a Prohibited Country, and will not export or re-export to */
/* any Prohibited Country or Denied Party. */
// Copyright 2003 VoteHere Inc. All Rights Reserved.

/*
 * class file_contents
 *
 * A silly-simple little class to make it easy to read in the contents
 * of a file and use it in as a string.
 *
 * Possible usage: cout << file_contents("filename.txt") << endl;
 *
 * Revision History
 * 	 who		 when		 what
 *	andrewb		11/07/2000	Initial code.
 *	andrewb		13/07/2000	Fixed dumb bug where it was using
 *					the string "INPUT" as the name of
 *					the input file.
 *	andrewb		16/10/2001	Improved to throw exception when
 *					there is a problem reading the
 *					file.
 *  leonard     03/12/2001  TT 1654: fixed a memory leak
 *
 */

#include <string>

#include <sys/types.h>
#include <sys/stat.h>
#include <stdio.h>
#include <errno.h>
#include "misc/vh_excpt.h"
#include "misc/array.h"

namespace VHUtil {

class file_contents
{
public:
  file_contents(const std::string & filename)
    : m_filename(filename)
  {
    struct stat statbuf;
    FILE * f = ::fopen(filename.c_str(), "rb");
    if (! f) throw VH_exception(errno, filename.c_str());
    
    if (::fstat(::fileno(f), & statbuf)) {
        throw VH_exception(errno, filename.c_str());
    }
    size_t len = statbuf.st_size;
    
	VHUtil::array<char> c(len);
    
    if (::fread(c.m_data, 1, len, f) != len) {
      throw VH_exception(ferror(f), filename.c_str());
    }
    
    m_contents = std::string(c.m_data, len);
    
    ::fclose(f);
  }
  operator std::string &(void) { return m_contents; }
private:
  std::string m_contents;
  std::string m_filename;
};

};
