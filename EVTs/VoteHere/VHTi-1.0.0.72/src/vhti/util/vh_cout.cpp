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

#if defined(_WIN32)
#include <windows.h>
#endif
#include <misc/vh_cout.h>
#include <fstream>
#include <iostream>
#include <sstream>

#define WIN32_LEAN_AND_MEAN             // Exclude rarely-used stuff from Windows headers

#ifdef WIN32
template <class _E,
class _Tr = std::char_traits<E>,
class _A = std::allocator<E> >
class basic_debugstringbuf
      : public std::basic_stringbuf <_E, _Tr, _A>
{
public:
   explicit basic_debugstringbuf(void)
      : std::basic_stringbuf <_E, _Tr, _A> (std::ios::out)
      {}
   virtual int_type sync()
      {
         sputc('\0'); // Required to keep leftover older lines from showing.
         OutputDebugString(str().data());
         seekoff(0, std::ios_base::beg);
         return 0;
      }
};

template <class _E,
class _Tr = std::char_traits<_E>,
class _A = std::allocator<_E> >
class basic_debugstream
      : public std::basic_iostream<_E, _Tr>
{
public:
   typedef std::basic_string<_E, _Tr, _A> _Mystr;
   explicit basic_debugstream(void)
      : std::basic_iostream<_E, _Tr>(&_Sb)
      {}
   virtual ~basic_debugstream()
      {}
   basic_debugstringbuf<_E, _Tr, _A> *rdbuf() const
      {
         return ((basic_debugstringbuf<_E, _Tr, _A> *)&_Sb);
      }
   _Mystr str() const
      {
         return (_Sb.str());
      }
   void str(const _Mystr& _S)
      {
         _Sb.str(_S);
      }
private:
   basic_debugstringbuf<_E, _Tr, _A> _Sb;
};

typedef basic_debugstream<char> debugstream;
#endif

class releasing_ostream
{
public:
   releasing_ostream(void) : m_ostream(NULL), m_allocated(true)
      { }
   ~releasing_ostream(void)
      {
         if (m_allocated)
            delete m_ostream;
      }
   releasing_ostream & operator = (std::ostream * o)
      {
         m_ostream = o;
         return *this;
      }
   bool operator ! (void)
      {
         return m_ostream == NULL;
      }
   operator std::ostream *(void)
      {
         return m_ostream;
      }
   void is_not_allocated(void)
      {
         m_allocated = false;
      }
private:
   std::ostream * m_ostream;
   bool m_allocated;
};

releasing_ostream m_cout;

std::ostream &
VHUtil::cout()
{
   // Describes where to direct the output
   char * c_debug_mode = getenv("DEBUG_MODE");
   if (!c_debug_mode)
      c_debug_mode = "";

   // A string representation of c_debug_mode
   std::string debug_mode(c_debug_mode);

   if (!m_cout)
   {
      if (debug_mode == "CON")
      {
         m_cout = &std::cout;
         m_cout.is_not_allocated();
      }
      else if (debug_mode == "ERR")
      {
         m_cout = &std::cerr;
         m_cout.is_not_allocated();
      }
      else if (debug_mode.substr(0, 5) == "file:")
      {
         // Parse over 5 characters to reach the file name.
         m_cout = new std::ofstream((debug_mode.substr(5)).c_str());
      }
#ifdef WIN32
#ifdef _DEBUG
      else if (debug_mode == "DEBUGGER")
      {
         m_cout = new debugstream;
      }
#endif
#endif
      else
      {
         m_cout = new std::ofstream("/dev/null");

         // there is no /dev/null under Windows!  so why does this
         // work? It's because operations on invalid streams are
         // treated as NOPs
      }
   }

   return *m_cout;
}

