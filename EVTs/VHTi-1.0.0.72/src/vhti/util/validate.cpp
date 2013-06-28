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

#include <util/validate.h>
#include <misc/vh_cout.h>
#include <misc/format_string.h>
#include <vhti/support.h>
#include <string>
#include <iostream>
#include <iomanip>
#include <cstdarg>

extern "C"
  {
#include <libxml/xmlmemory.h>
#include <libxml/parser.h>
#include <libxml/parserInternals.h>
#include <libxml/HTMLparser.h>
#include <libxml/HTMLtree.h>
#include <libxml/tree.h>
#include <libxml/xpath.h>
#include <libxml/debugXML.h>
#include <libxml/xmlerror.h>
  }

namespace
{
void
handle_validity_error(int* valid, const char * format, ...)
{
   // A list of all the arguments
   va_list args;
   va_start(args, format);
   // A formatted list of the arguments
   std::string formatted;
   VHUtil::vformat(formatted,format,args);
   va_end(args);

   VHUtil::cout() << "XML validity error:" << std::endl;
   VHUtil::cout() <<formatted<<std::endl;
   *valid = 0;
}

void
handle_validity_error_nolog(int* valid, const char * format, ...)
{
   *valid = 0;
}

void
handle_validity_warning(int* , const char *format, ...)
{
   // A list of all the arguments
   va_list args;
   va_start(args, format);
   // A formatted list of the arguments
   std::string formatted;
   VHUtil::vformat(formatted,format,args);
   va_end(args);

   VHUtil::cout() << "XML validity warning:" << std::endl;
   VHUtil::cout() <<formatted<<std::endl;
}

void
handle_validity_warning_nolog(::xmlParserCtxtPtr ctx, const char *format, ...)
{}

}

bool VHUtil::validate_xml_document(const std::string& doc, const std::string& dtd, bool logXMLProblems)
{
   // A pointer to a document tree
   ::xmlDocPtr doc_tree = 0;
   // A pointer to a dtd
   ::xmlDtdPtr DtdPtr=0;
   // A variable to hold a copy of the document
   char *copy_doc=0;
   // A pointer to a Parser Context
   ::xmlParserCtxtPtr ctxt=0;

   // A status flag
   bool preparation_complete = false;

   // Use `do' and `break' to avoid `goto's, which are prohibited by
   // some coding standards

   do
   {
      copy_doc = VHTI_dup(doc.c_str());

      ctxt=::xmlCreateMemoryParserCtxt(copy_doc, strlen(copy_doc));
      if (0 == ctxt)
         break;

      ctxt->sax->error= logXMLProblems ? (::errorSAXFunc) handle_validity_error : (::errorSAXFunc) handle_validity_error_nolog;
      ctxt->validate=0; // leonard 08.10.2001: we will make the call
                        // to do DTD validation ourselves later
                        // (otherwise DTD line is expected to be
                        // preesent in the XML)

      if (::xmlParseDocument(ctxt) !=0 || ctxt->valid==0)
         break;

      if(!(doc_tree = ctxt->myDoc))
         break;

      /*
       * IMPORTANT NOTE:
       *
       * dtdBuf is freed by libxml at end of parse, so there is no
       * leak here.
       */

      ::xmlParserInputBufferPtr dtdBuf = ::xmlParserInputBufferCreateMem (dtd.c_str(), dtd.size(),
                                                                          XML_CHAR_ENCODING_NONE);

      if(! dtdBuf)
         break;

      if(!(DtdPtr = ::xmlIOParseDTD(NULL, dtdBuf,
                                    XML_CHAR_ENCODING_NONE   )))
         break;

      preparation_complete = true;
   }
   while(0);

   // A validity flag
   bool valid=false;
   if (preparation_complete)
   {
      // A Valid Context object
      ::xmlValidCtxt cvp;
      ::memset (&cvp, 0, sizeof (cvp));
      cvp.userData = &valid;
      cvp.error    = logXMLProblems ? (::xmlValidityWarningFunc) handle_validity_error : (::xmlValidityWarningFunc) handle_validity_error_nolog ;
      cvp.warning  = logXMLProblems ? (::xmlValidityWarningFunc) handle_validity_warning : (::xmlValidityWarningFunc) handle_validity_warning_nolog ;

      valid=(::xmlValidateDtd(&cvp, doc_tree, DtdPtr)==1);
   }

   if ( copy_doc)
      VHTI_free (copy_doc);
   if ( DtdPtr)
      ::xmlFreeDtd(DtdPtr);
   if ( doc_tree)
      ::xmlFreeDoc(doc_tree);
   if ( ctxt )
      ::xmlFreeParserCtxt(ctxt);

   ::xmlCleanupParser ();

   return valid;
}
