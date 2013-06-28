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

#if defined (_MSC_VER)
# pragma warning (disable: 4786)
#endif

#include <iostream>

#include <util/dirit.h>
#include <misc/vh_excpt.h>
#include <cerrno>

#if defined (_WIN32)
#include <sstream>
namespace {
std::string itos (int i)
{
   // A stream to hold the integer
   std::ostringstream tmp;
   tmp << i;
   return tmp.str ();
}
}
#endif

namespace VHUtil{

DirectoryIterator::DirectoryIterator(const std::string& dir)
   : m_directory(dir),
#if defined(_WIN32)
     m_hFile(-1)
#else
   m_dp(0),
   m_dirent(0)
#endif
{
#if defined(_WIN32)
   // A string to hold the directory path
   const std::string filter(m_directory+"/*");

   m_hFile=::_findfirst(filter.c_str(),&c_file);
   if ( m_hFile==-1 )
   {
      throw Exception(__FILE__,__LINE__,"UTIL_FINDFIRST_FAILED",itos(errno).c_str(),filter.c_str());
   }
#else

   m_dp=::opendir(m_directory.c_str());
   if ( m_dp )
      m_dirent=::readdir(m_dp);

   if ( m_dp==0 || m_dirent==0 )
   {
      throw Exception(__FILE__,__LINE__,"UTIL_READING_DIRECTORY",m_directory.c_str());
   }
#endif
}


bool DirectoryIterator::getF(std::string& f)
{
#if defined(_WIN32)
   // A flag to indicate if the iteration is done
   bool done=false;

   while ( std::string(".")==c_file.name || // A string to indicate the current directory
           std::string("..")==c_file.name ) // A string to indicate the parent directory
   {
      done=Next();
      if ( done )
      {
         break;
      }
   }

   if ( !done )
   {
      f=m_directory+'/'+c_file.name;
   }

   return done;
#else
   // A flag to indicate if the iteration is done
   bool done=false;

   while ( std::string("." )==m_dirent->d_name || // A string to indicate the current directory
           std::string("..")==m_dirent->d_name ) // A string to indicate the parent directory
   {
      done=Next();
      if ( done )
      {
         break;
      }
   }

   if ( !done )
   {
      f=m_directory+'/'+m_dirent->d_name;
   }

   return done;
#endif
}

bool DirectoryIterator::Next(void)
{
#if defined(_WIN32)
   // The error number
   int err=::_findnext(m_hFile,&c_file);

   return (err == -1) && (errno == ENOENT);
#else
   m_dirent=::readdir(m_dp);

   return m_dirent==0;
#endif
}

DirectoryIterator::~DirectoryIterator(void)
{
#if defined(_WIN32)
   if ( m_hFile!=-1 )
      (void) ::_findclose(m_hFile);
#else
   if ( m_dp )
      (void) ::closedir(m_dp);
#endif
}


}
