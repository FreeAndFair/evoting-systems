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

#if !defined(_UTIL_EXCPT_H)
#define _UTIL_EXCPT_H

#include <misc/result.h>
#include <iosfwd>
#include <stdexcept>

/************************
 * A word about error handling inside of VHTI functions.
 *
 * Throw a VH_exception anyplace you'd normally want to immediatly report
 * an error condition and then exit.  
 * 
 * throw VH_exception("BAD_THING_HAPPENED");
 * 
 * Use VH_assert just like you would any assert macro:  it will throw a
 * VHUtil::Exception if its expression is zero.  As much as is feasible,
 * VH_nonzero should be used instead of VH_assert.
 *
 * Use VH_zero and VH_nonzero to check that something is either zero or
 * nonzero.  These are better than VH_assert because they will throw their
 * 'arg' parameter (converted to a string) if they fail, rather than the
 * expression they are checking.  
 *
 * Use VH_propagate anytime a VHTI_* function is being called from inside
 * of a VHTI_* function.  It will propigate the error condition up to the
 * enclosing VHTI_* function, so that both errors will be returned to the
 * caller.
 ***********************/

#define VH_exception (VHUtil::Exception_Creator(__FILE__, __LINE__))

#define VH_assert(exp)      (void)( (  exp ) || (VHUtil::_assert(#exp, __FILE__, __LINE__), 0) )
#define VH_zero(exp,arg)    (void)( (!(exp)) || (VHUtil::_check (#arg, __FILE__, __LINE__), 0) )
#define VH_nonzero(exp,arg) VH_zero(!(exp),arg)
#define VH_propagate(exp,arg) if (exp)                            \
{                                                                 \
   std::string whine = internal_get_last_error ();                \
   whine += " : ";                                                \
   whine += #arg;                                                 \
   throw VHUtil::Exception (__FILE__, __LINE__, whine.c_str ());  \
}

namespace VHUtil{

class Exception : public std::exception, public Result
{
public:
   Exception(const char * file, int line, int exceptno); /* use when no parameters: probably usually */
   Exception(const char * file, int line, const char * exceptid);

   Exception(const char * file, int line, int exceptno, const parameters_t& parameters);
   Exception(const char * file, int line, const char * exceptid, const parameters_t& parameters);

   Exception(const char * file, int line, int exceptno,
             const char * arg0,
             const char * arg1 = 0,
             const char * arg2 = 0,
             const char * arg3 = 0,
             const char * arg4 = 0);
   Exception(const char * file, int line, const char * exceptid,
             const char * arg0,
             const char * arg1 = 0,
             const char * arg2 = 0,
             const char * arg3 = 0,
             const char * arg4 = 0);

   Exception(const char * file, int line, int exceptno,
             VHUtil::have_context_t d,
             const char * arg0,
             const char * arg1 = 0,
             const char * arg2 = 0,
             const char * arg3 = 0,
             const char * arg4 = 0,
             const char * arg5 = 0);
   Exception(const char * file, int line, const char * exceptid,
             VHUtil::have_context_t d,
             const char * arg0,
             const char * arg1 = 0,
             const char * arg2 = 0,
             const char * arg3 = 0,
             const char * arg4 = 0,
             const char * arg5 = 0);

   Exception(const char * file, int line, int exceptno, int arg0);
   Exception(const char * file, int line, const char * exceptid, int arg0);

   int getLine(void) const { return m_line; }
   const std::string& getFile(void) const { return m_file; }

   virtual VHUtil::Exception::~Exception() throw () {};
   virtual const char * what(void) const throw ();
   std::string getWhat(void) const;

   // note that the << operator onto streams is also available
   void DumpToStream(std::ostream& os);

   std::string get_result_string(void) const;

protected:
   bool LookupFormat(std::string& formatStr, int excptno) const;
protected:
   std::string m_file; // file where throw begins
   int m_line; // line in file where throw begins
   mutable std::string m_what;
};

class Exception_Creator
{
public:
   Exception_Creator(char * file, int line)
      : m_file(file), m_line(line) {};
   Exception operator () (int exceptno, const char * arg0 = 0,
                          const char * arg1 = 0, const char * arg2 = 0,
                          const char * arg3 = 0, const char * arg4 = 0)
      {
         return Exception(m_file, m_line, exceptno,
                          arg0, arg1, arg2, arg3, arg4);
      }
   Exception operator () (const char * exceptid, const char * arg0 = 0,
                          const char * arg1 = 0, const char * arg2 = 0,
                          const char * arg3 = 0, const char * arg4 = 0)
      {
         return Exception(m_file, m_line, exceptid,
                          arg0, arg1, arg2, arg3, arg4);
      }

private:
   const char * m_file;
   int m_line;
};

inline void
_assert(char * msg, char * file, int line)
{
   throw Exception(file, line, "vhutil::ASSERTION_FAILED", msg);
}

inline void
_check(const char * arg, const char * file, int line)
{
   throw Exception(file, line, arg);
}

} // namespace VHUtil

std::ostream & operator <<(std::ostream& os, VHUtil::Exception& e);

#endif

