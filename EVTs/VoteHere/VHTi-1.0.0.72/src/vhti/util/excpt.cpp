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

#include <misc/vh_excpt.h>
#include <iostream>
#include <iomanip>
#include <sstream>

namespace {
   std::string make_context (const char *file, int line)
   {
      // A stream to hold the context
      std::stringstream tmpContext;
      tmpContext << "In file " << file << ", line " << line;
      return tmpContext.str ();
   }
}

namespace VHUtil{

Exception::Exception(const char* file, int line, int exceptno) :
   Result(exceptno), m_file(file), m_line(line)
{
   setContext (make_context (file, line));
}

Exception::Exception(const char* file, int line, const char * exceptid) :
   Result(exceptid), m_file(file), m_line(line)
{
   setContext (make_context (file, line));
}

Exception::Exception(const char* file, int line, int exceptno, const parameters_t& parameters) :
   Result(exceptno,parameters),
   m_file(file),
   m_line(line)
{
   setContext (make_context (file, line));
}

Exception::Exception(const char* file, int line, const char * exceptid, const parameters_t& parameters) :
   Result(exceptid,parameters),
   m_file(file),
   m_line(line)
{
   setContext (make_context (file, line));
}

Exception::Exception(const char* file, int line, int exceptno,
                     const char *arg0,
                     const char *arg1 ,
                     const char *arg2 ,
                     const char *arg3 ,
                     const char *arg4 ) :
   Result(exceptno, arg0, arg1, arg2, arg3, arg4),
   m_file(file),
   m_line(line)
{
   setContext (make_context (file, line));
}

Exception::Exception(const char* file, int line, const char * exceptid,
                     const char *arg0,
                     const char *arg1 ,
                     const char *arg2 ,
                     const char *arg3 ,
                     const char *arg4 ) :
   Result(exceptid, arg0, arg1, arg2, arg3, arg4),
   m_file(file),
   m_line(line)
{
   setContext (make_context (file, line));
}


Exception::Exception(const char* file, int line, int exceptno,
                     VHUtil::have_context_t d,
                     const char *arg0,
                     const char *arg1 ,
                     const char *arg2 ,
                     const char *arg3 ,
                     const char *arg4 ,
                     const char *arg5 ) :
   Result(exceptno, arg1, arg2, arg3, arg4, arg5),
   m_file(file),
   m_line(line)

{
   setContext(arg0);
}

Exception::Exception(const char* file, int line, const char * exceptid,
                     VHUtil::have_context_t d,
                     const char *arg0,
                     const char *arg1 ,
                     const char *arg2 ,
                     const char *arg3 ,
                     const char *arg4 ,
                     const char *arg5 ) :
   Result(exceptid, arg1, arg2, arg3, arg4, arg5),
   m_file(file),
   m_line(line)

{
   setContext(arg0);
}

Exception::Exception(const char* file, int line, int exceptno, int arg0) :
   Result(exceptno, arg0),
   m_file(file),
   m_line(line)
{
   setContext (make_context (file, line));
}

Exception::Exception(const char* file, int line, const char * exceptid, int arg0) :
   Result(exceptid, arg0),
   m_file(file),
   m_line(line)
{
   setContext (make_context (file, line));
}

void Exception::DumpToStream(std::ostream& os)
{
   os <<"file:     "<<m_file<<std::endl;
   os <<"line:     "<<m_line<<std::endl;
   os <<"what:     "<<getWhat()<<std::endl;
   os <<"errno:    "<<m_resultno<<std::endl;
   if ( !m_context.empty() )
   {
      os << "context: `"
         << m_context
         << "'"
         << std::endl;
   }
   // The number of parameters
   const unsigned nparams=nParameters();
   os <<"# params: "<<nparams<<std::endl;
   for(unsigned i=0; i<nparams; ++i)
   {
      os <<"param #"<<i<<": "<<getParameter(i)<<std::endl;
   }
}

bool Exception::LookupFormat(std::string& formatStr, int /* ignored */) const
{
   if (-1 != m_resultno) {
      formatStr=Result::mlt_message_from_error(m_resultno);
   } else {
      formatStr = "Unknown error: " + m_resultid;
   }

   return true;
}

std::string Exception::get_result_string(void) const
{
   return Result::get_result_string(m_resultno,m_parameters);
}

const char* Exception::what(void) const throw ()
{
   if ( m_what.empty() )
   {
      m_what=getWhat();
   }

   return m_what.c_str();
}

std::string Exception::getWhat() const
{
   // Lookup format string
   // replace %s's with parameters
   std::string formatted;
   // A flag to indicate if we got the format
   bool gotFormat=LookupFormat(formatted,m_resultno);
   if ( gotFormat )
   {
      formatted=Format(formatted,m_parameters);
   }
   if(! m_context.empty())
   {
      formatted += "; Context: `" + m_context;
      formatted += "'";
   }
   return formatted;
}

}

std::ostream & operator <<(std::ostream& os, VHUtil::Exception& e)
{
   e.DumpToStream(os);
   return os;
}

