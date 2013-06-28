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

#if !defined(_UTIL_DIRIT_H)
#define _UTIL_DIRIT_H

/*! \file
 */

//
// util/dirit.h
//
// this is not an ideal iterator since it does
// not respect the STL semantics
//
// Revision History
//   leonard 26.04.2001 class implemented for TT 825
//   leonard 30.07.2001 moved from transcript -> util 

#include <string>

#if defined(_WIN32)
#include <io.h>
#else
#include <dirent.h>
#endif

namespace VHUtil{

class DirectoryIterator{
public:
	DirectoryIterator(const std::string& dir);
	~DirectoryIterator(void);

	//! get fullpath of current file in iteration; return false if done iteration
	bool getF(std::string& f);
	//! returns true when iteration is complete
	bool Next(void);
private:
	const std::string m_directory;
#if defined(_WIN32)
	struct ::_finddata_t c_file;
	long m_hFile;
#else
	::DIR* m_dp;
	::dirent* m_dirent;
#endif
};

} // namespace VHUtil 

#endif
