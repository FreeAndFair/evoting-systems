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

#if !defined(_UTIL_RESULT_HPP)
#define _UTIL_RESULT_HPP

#include <string>
#include <vector>

namespace VHUtil{

class xml_tree;

typedef enum { 
   have_context
} have_context_t;

class Result {
public:
   typedef std::string parameter_t; 
   typedef std::vector<parameter_t> parameters_t;

   /* Each overloaded version has a resultno and a resultid version. */
   Result(int resultno); /* use when no parameters: probably usually */ 
   Result(const char * resultid);

   Result(int resultno, const parameters_t& parameters); 
   Result(const char * resultid, const parameters_t& parameters); 

   Result(int resultno, const char *arg0,
          const char *arg1 =0,
          const char *arg2 =0,
          const char *arg3 =0,
          const char *arg4 =0);
   Result(const char * resultid, const char *arg0,
          const char *arg1 =0,
          const char *arg2 =0,
          const char *arg3 =0,
          const char *arg4 =0);

   Result(int resultno, 
          VHUtil::have_context_t d,
          const char *arg0,
          const char *arg1 =0,
          const char *arg2 =0,
          const char *arg3 =0,
          const char *arg4 =0,
          const char *arg5 =0);
   Result(const char * resultid, 
          VHUtil::have_context_t d,
          const char *arg0,
          const char *arg1 =0,
          const char *arg2 =0,
          const char *arg3 =0,
          const char *arg4 =0,
          const char *arg5 =0);

   Result(int resultno, int arg0);
   Result(const char * resultid, int arg0);

   virtual ~Result(); 

   std::string getErrID(void);
   int getResultNo(void ) const { return m_resultno; }
   std::string getResultId(void) const { return m_resultid; }
   std::string getNamespace(const std::string & id) const;
   std::string getResultNamespace(void) const 
      { return getNamespace(m_resultid);};
   std::string getName(const std::string & id) const;
   std::string getResultName(void) const 
      { return getName(m_resultid);};
   const parameters_t& getParameters(void) const { return m_parameters; }
   unsigned nParameters(void) const { return m_parameters.size(); }
   const parameter_t& getParameter(unsigned i) const 
      { return m_parameters[i]; }
  
   std::string get_result_string(void) const;
   std::string getContext(void) const { return m_context; }
   void setContext(const std::string& c) 
      { m_context += (std::string(" ")+c); }
   void clearContext() { m_context = (std::string(" ")); }
   void setResultNo(int resultNo) {m_resultno = resultNo; }
   void setParameters(const parameters_t& params) { m_parameters=params; }

   int lookupResultNo(const char * resultid);
   std::string lookupResultId(int resultno);

   // replace occurences of %s in formatStr with the values from parameters
   std::string Format(const parameters_t& parameters) const;
   std::string Format(const std::string& formatStr, const parameters_t& parameters) const;
   std::string Format(int, const parameters_t& parameters) const;
   std::string Format(void) const;
   // format as DDDDDD__param&param&param
   std::string get_result_string(int resulttno, const parameters_t& parameters) const;
   std::string mlt_message_from_error(int) const;
   void init(void);
   void set_language(std::string l);

   static void load_errors_all_xml(void);
   static void load_errors_one_xml(const char *);

   typedef std::vector<xml_tree *> XMLTreesVector_t;

   static bool s_treesInitialized;
   static XMLTreesVector_t s_xml_trees;
   static void UnloadTrees(void);
protected:
   static void load_errors_from_xml(const char *);
#if defined(_WIN32)
   static bool load_errors_from_resource(int id);
#endif

   int m_resultno;
   std::string m_resultid;
   std::string m_context;
   std::string m_language;
   std::vector<std::string> m_parameters;
};

}

#endif

