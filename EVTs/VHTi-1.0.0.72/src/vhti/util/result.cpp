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

#include <util/dirit.h>
#include <misc/xml_tree.h>
#include <misc/result.h>
#include <misc/array.h>
#include "../support/support_internal.h"

#include <sstream>
#include <iostream>
#include <iomanip>
#include <stdexcept>
#include <stdio.h>

#include <cerrno>
//#include "common_paths.h"

namespace {

// Code for the default language
const char* ERRMSG_DEFAULT_LANGUAGE="EN";
// Path for error messages
const char* VH_ERRMSG_XML_PATH="VH_ERRMSG_XML_PATH";

}

VHUtil::Result::XMLTreesVector_t VHUtil::Result::s_xml_trees;
bool VHUtil::Result::s_treesInitialized=false;

namespace VHUtil{

/*
 * Each of the constructors must call a lookupResultXx function
 * because that is where init() gets called to load the xml files the
 * first time.  Each of the constructors must call one of the
 * lookupResultXx functions anyhow, because they only ever take a no
 * or an id, so the other one must be looked up.
 */

Result::Result (int resultno)
   : m_resultno(resultno)
{
   m_resultid = lookupResultId(resultno);
}

Result::Result (const char * resultid)
   : m_resultid(resultid)
{
   m_resultno = lookupResultNo(resultid);
}

Result::Result (int resultno, const parameters_t& parameters)
   : m_resultno(resultno),
     m_parameters(parameters)
{
   m_resultid = lookupResultId(resultno);
}

Result::Result (const char * resultid, const parameters_t& parameters)
   : m_resultid(resultid),
     m_parameters(parameters)
{
   m_resultno = lookupResultNo(resultid);
}

Result::Result (int resultno, const char *arg0,
 const char *arg1 ,
 const char *arg2 ,
 const char *arg3 ,
 const char *arg4 )
   : m_resultno(resultno)
{
   m_resultid = lookupResultId(resultno);

   parameters_t tmp_params;
   if(arg0)
      tmp_params.push_back(arg0);
   if(arg1)
      tmp_params.push_back(arg1);
   if(arg2)
      tmp_params.push_back(arg2);
   if(arg3)
      tmp_params.push_back(arg3);
   if(arg4)
      tmp_params.push_back(arg4);
   setParameters(tmp_params);
}

Result::Result (const char * resultid, const char *arg0,
 const char *arg1,
 const char *arg2,
 const char *arg3,
 const char *arg4)
   : m_resultid(resultid)
{
   m_resultno = lookupResultNo(resultid);

   parameters_t tmp_params;
   if(arg0)
      tmp_params.push_back(arg0);
   if(arg1)
      tmp_params.push_back(arg1);
   if(arg2)
      tmp_params.push_back(arg2);
   if(arg3)
      tmp_params.push_back(arg3);
   if(arg4)
      tmp_params.push_back(arg4);
   setParameters(tmp_params);
}

Result::Result (int resultno, VHUtil::have_context_t d,
 const char *arg0,
 const char *arg1,
 const char *arg2,
 const char *arg3,
 const char *arg4,
 const char *arg5)
   : m_resultno(resultno)
{
   m_resultid = lookupResultId(resultno);

   parameters_t tmp_params;
   setContext(arg0);
   if(arg1)
      tmp_params.push_back(arg1);
   if(arg2)
      tmp_params.push_back(arg2);
   if(arg3)
      tmp_params.push_back(arg3);
   if(arg4)
      tmp_params.push_back(arg4);
   if(arg5)
      tmp_params.push_back(arg5);
   setParameters(tmp_params);
}

Result::Result (const char * resultid, VHUtil::have_context_t d,
 const char *arg0,
 const char *arg1,
 const char *arg2,
 const char *arg3,
 const char *arg4,
 const char *arg5)
   : m_resultid(resultid)
{
   m_resultno = lookupResultNo(resultid);

   parameters_t tmp_params;
   setContext(arg0);
   if(arg1)
      tmp_params.push_back(arg1);
   if(arg2)
      tmp_params.push_back(arg2);
   if(arg3)
      tmp_params.push_back(arg3);
   if(arg4)
      tmp_params.push_back(arg4);
   if(arg5)
      tmp_params.push_back(arg5);
   setParameters(tmp_params);
}

Result::Result (int resultno, int arg0)
   : m_resultno(resultno)
{
   m_resultid = lookupResultId(resultno);

   // A parameters object
   parameters_t params;

   // A stream to hold the arguments
   std::ostringstream oss;
   oss <<arg0;

   parameter_t param(oss.str());
   params.push_back(param);

   setParameters(params);
}

Result::Result (const char * resultid, int arg0)
   : m_resultid(resultid)
{
   m_resultno = lookupResultNo(resultid);

   // A parameters object
   parameters_t params;

   // A stream to hold the arguments
   std::ostringstream oss;
   oss <<arg0;

   parameter_t param(oss.str());
   params.push_back(param);

   setParameters(params);
}

Result::~Result (void)
{
}

int
Result::lookupResultNo (const char * resultid)
{
   init();

   // strings to hold the namespace and the name of the resultid
   const std::string space(getNamespace(resultid));
   const std::string name(getName(resultid));

   // A return value
   int result = -1;

   if (space.size() && name.size()) do {
      // A flag to indicate if we are returning from the function
      int returning = 0;
      if(s_xml_trees.empty()) {

         break;
      }
      // How many xml trees you have
      int n_xml = s_xml_trees.size();
      for(int j = 0; j < n_xml && ! returning; j++) {
         // The root node of the current xml tree
         VHUtil::xml_node  rt_nd = s_xml_trees[j]->root();
         // One level below the errors element is the errorlist element series
         if(rt_nd->name() != "errors") {
            returning = 1;
            break;
         }
         // Search for the matching error code in errorlist

         // The node with the correct namespace
         VHUtil::xml_node el_nd = rt_nd->element("errorlist", "componentid", space);
         if (NULL == el_nd)
            continue;

         // Then node with the correct the name within the namespace.
         VHUtil::xml_node er_nd = el_nd->element("error", "errid", name);
         if (NULL == er_nd)
            continue;

         if (er_nd->has_attribute("num"))
            result = VHInternal::int_from_attribute (er_nd, "num");

         // Found the correct error, now we're done.
         returning = 1;
         break;
      }
   } while(0);

   return result;
}

std::string
Result::lookupResultId (int resultno)
{
   init();
   // Default text
   std::string def_text = "Unknown error";
   // A string to hold the namespace
   std::string space;
   // A string to hold the name
   std::string name;
   do {
      // A flag to indicate if we are returning from the function
      int returning = 0;
      if(s_xml_trees.empty()) {
         def_text = "XML error files not installed";
         break;
      }
      // How many xml trees you have
      int n_xml = s_xml_trees.size();
      for(int j = 0; j < n_xml && ! returning; j++) {
         VHUtil::xml_node  rt_nd = s_xml_trees[j]->root();
         // One level below the errors element is the errorlist element series
         if(rt_nd->name() != "errors") {
            returning = 1;
            break;
         }
         // Search for the matching error code in errorlist
         // The node with the matching error code
         VHUtil::xml_node el_nd = NULL;
         for (int k = 0; (el_nd = rt_nd->element("errorlist", k)); k ++) {

            space = el_nd->attribute("componentid");
            // A char to hold the result number
            char num[10];
            sprintf(num, "%d", resultno);
            // A node with the correct result number
            VHUtil::xml_node er_nd = el_nd->element("error", "num", num);
            if (er_nd) {
               name = er_nd->attribute("errid");
               def_text = space + ':' + name;
               returning = 1;
               break;
            }
         }
      }
   } while(0);

   return def_text;
}

/*
 * Use the mlt format string from the xml file
 */
std::string
Result::Format (const parameters_t& parameters) const
{
   // A string to hold the result format
   std::string format = mlt_message_from_error(m_resultno);
   return Format(format, parameters);
}

std::string
Result::Format (const std::string& formatStr, const parameters_t& parameters) const
{
   // A string from the formatted string input
   std::string formatted(formatStr);
   // An iterator for the string
   std::string::size_type cursor=0;
   // The current parameter
   unsigned curParam=0;

   while ( cursor!=std::string::npos )
   {
      cursor=formatted.find(std::string("%s"),cursor);

      if ( cursor!=std::string::npos  )
      {
         formatted.replace(cursor,2,parameters.at(curParam++));
      }
   }

   return formatted;
}

std::string Result::Format(void) const
{
   return Format(m_parameters);
}

std::string Result::get_result_string(int resultno, const parameters_t& parameters) const
{
   // A stream for the Result output
   std::ostringstream oss;
   oss <<std::setw(6)<<std::setfill('0')<<resultno<<' '<<' ';
   // How many parameters the result has
   const unsigned nparams=parameters.size();
   oss << getContext();
   oss <<'&';
   for(unsigned i=0; i<nparams; ++i)
   {
      oss <<parameters[i];
      oss <<'&';
   }

   return oss.str();
}

std::string Result::get_result_string(void) const
{
   return get_result_string(m_resultno, m_parameters);
}

void Result::init(void)
{
   if ( !s_treesInitialized )
   {
      m_language = ERRMSG_DEFAULT_LANGUAGE;
      load_errors_all_xml();

      s_treesInitialized=true;
   }
}

void Result::set_language(std::string l)
{
   m_language = l;
}

void Result::load_errors_from_xml(const char* xml)
{
   // An xml tree auto pointer
   std::auto_ptr<xml_tree> tree(new xml_tree(xml, xml_tree::NO_THROW));
   if(! tree->parsed_OK ())
      throw std::runtime_error("Couldn't parse XML in error message file");
   s_xml_trees.push_back(tree.release());
}

void Result::load_errors_one_xml(const char *fpath)
{
   // A file to hole the error messages
   FILE *f;
   // The file length
   long int flen;

   if(! (f = fopen(fpath, "rb")))
      throw std::runtime_error("Can't open XML error message file");

   if( fseek(f, 0, SEEK_END) < 0) {
      fclose(f);
      throw std::runtime_error("Can't seek to end of XML error message file");
   }

   if( (flen = ftell(f)) < 0 ){
      fclose(f);
      throw std::runtime_error("Can't determine size of XML error message file");
   }

   rewind(f);

   // An array of characters for the buffer
   array<char> buf(flen+1);
   // The size of the buffer that is read
   int nRead;
   if((nRead=fread(buf.m_data, sizeof(char), flen, f)) != flen) {
      fclose(f);
      throw std::runtime_error("Can't read XML error message file");
   }
   fclose(f);
   *(buf.m_data + flen) = 0;

   load_errors_from_xml(buf);
}

/*
 *
 * mlt_message_from_error
 *
 * Return the selected error message in the selected language, or
 * the default language if it does not exist in the desired language.
 * If there is no MLT for the error, return the symbolic identifier.
 * If the error is not found in the xml error message document,
 * return the string "Unknown error"
 */

std::string Result::mlt_message_from_error(int err) const
{
   // Default text
   std::string def_text = "Unknown error";
   // Characters to hold the error number
   char num[10];
   sprintf(num, "%d", err);

   def_text += ": ";
   def_text += num;

   do {
      // A flag to indicate if we are returning from the function
      int returning = 0;
      if(s_xml_trees.empty()) {
         def_text = "XML error files not installed";
         break;
      }
      // The number of xml trees we have
      int n_xml = s_xml_trees.size();
      for(int j = 0; j < n_xml && ! returning; j++) {
         // The root node of s_xml_trees
         VHUtil::xml_node  rt_nd = s_xml_trees[j]->root();
         // One level below the errors element is the errorlist element series
         if(rt_nd->name() != "errors") {
            returning = 1;
            break;
         }
         // The node with the matching error code in errorlist
         VHUtil::xml_node el_nd;
         for (unsigned k = 0; (el_nd = rt_nd->element(k)); k ++) {

            // A node with the correct result number
            VHUtil::xml_node er_nd = el_nd->element("error", "num", num);
            if (! er_nd)
               continue;

            // A node with the correct language referenct
            VHUtil::xml_node mlt_nd = er_nd->element("mlterrortext", "langref", m_language);
            if (mlt_nd) {
               def_text = mlt_nd->characters();
               returning = 1;
               break;
            }

            mlt_nd = er_nd->element("mlterrortext", "langref", ERRMSG_DEFAULT_LANGUAGE);
            if (mlt_nd) {
               def_text = mlt_nd->characters();
               returning = 1;
               break;
            }

            returning = 1;
         }
      }
   } while(0);

   return def_text;
}

std::string Result::getErrID(void)
{
   // Return string
   std::string rv = "Unknown error";

   if (m_resultid.size())
   {
   }
   else if (m_resultno != -1)
   {
   }

   if( s_xml_trees.empty() )
   {
      rv="XML error files not installed";
   }
   else
   {
      for(XMLTreesVector_t::iterator ii = s_xml_trees.begin(); ii!=s_xml_trees.end(); ++ii)
      {
         xml_node  root = (*ii)->root();
         if ( root==0 )
            break;

         // One level below the errors element is the errorlist element series
         if(root->name() != "errors")
         {
            rv="Invalid XML errors file";
            break;
         }

         // Search for the matching error code in errorlist
         xml_node el = root->element(0);
         if ( el==0 )
            break;

         // Found error flag
         bool foundErrID=false;

         for(unsigned i = 0; el->element(i); ++i)
         {
            if( m_resultno != VHInternal::int_from_attribute (el->element(i), "num"))
               continue;

            if(el->element(i)->has_attribute("errid"))
            {
               rv=el->element(i)->attribute("errid");
               foundErrID=true;
               break;
            }
         }

         if ( foundErrID )
         {
            break;
         }
      }
   }

   return rv;
}

std::string
Result::getNamespace(const std::string & id) const
{
   // An iterator for the id string
   std::string::size_type p = id.find(":");
   // The result string
   std::string result;
   if (p) {
      result = id.substr(0, p);
   } else {
      result = "";
   }
   return result;
}

std::string
Result::getName(const std::string & id) const
{
   // An iterator for the id string
   std::string::size_type p = id.find(":");
   // The result string
   std::string result;
   if (p) {
      result = id.substr(p + 1);
   } else {
      result = "";
   }
   return result;
}

void
Result::load_errors_all_xml(void)
{
   // The path string
   std::string path;
   // A char to hold an environment variable value
   const char *env_p=0;

   env_p = ::getenv(VH_ERRMSG_XML_PATH);

   if( env_p )
      path = env_p;
   else
      path = "."; // BUGBUG -- better to load a single xml file

   // A directory iterator object
   DirectoryIterator dit(path);
   // The path of the file
   std::string filepath;
   while (dit.getF(filepath) == true) {
      load_errors_one_xml(filepath.c_str());
      if (dit.Next())
         break;
   }
}

void Result::UnloadTrees(void)
{
   // this function exists to help remove noise during memory leak checking

   for(XMLTreesVector_t::iterator ii=s_xml_trees.begin(); ii!=s_xml_trees.end(); ++ii)
   {
      delete (*ii);
   }
}

}

