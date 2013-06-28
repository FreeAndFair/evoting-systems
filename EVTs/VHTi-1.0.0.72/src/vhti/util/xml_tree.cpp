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

#include <libxml/xmlversion.h>
#if  (LIBXML_VERSION > 20504) && (LIBXML_VERSION < 20603)
# define LIBXML_THREAD_ENABLED 1
#endif
#include <libxml/entities.h>
#include <misc/xml_tree.h>
#include <misc/array.h>
#include <misc/vh_cout.h>
#include <misc/vh_excpt.h>
#include <pki/pki_internal.h>
#include <vhti/sign.h>
#include <vector>
#include <iostream>
#include <sstream>
#include <algorithm>
#include <cassert>
#include <cstdarg>

namespace {

   std::string
   entityify (const std::string & s)
   {
      std::string return_value;
      xmlChar *ascii = xmlEncodeEntitiesReentrant (NULL,
                                                   (const xmlChar *)s.c_str ());
      
      return_value = (const char *)ascii;
      xmlFree (ascii);
      return return_value;
   }

   // string is a sequence of UTF-8-encoded bytes.  TODO: std::string
   // is defined to contain plain characters, but we are interpreting
   // them as unsigned with a static_cast.  It'd be nice to be able to
   // eliminate that cast.
   //
   // throw an exception if the string contains control characters
   // other than tab, carriage-return, and linefeed.
   const std::string &
   throw_if_non_utf8 (const std::string & s)
   {
      for (std::string::const_iterator it = s.begin();
           it != s.end(); it ++)
      {
         const unsigned char this_byte = static_cast<unsigned char> (* it);

         if ((this_byte < 0x20)
             && (0x09 != this_byte) // tab
             && (0x0A != this_byte) // linefeed
             && (0x0D != this_byte)) // carriage-return
            throw VH_exception ("XML_CHAR_ERROR");
      }
      return s;
   }

// leonard 20.05.2002 need this class otherwise
//                    NodeRemovalCondition in remove_children_if
//                    gets sliced and we end up calling a pure virtual function
   class RemovalPredicate{
   private:
      VHUtil::NodeRemovalCondition& m_condition;
   public:
      RemovalPredicate(VHUtil::NodeRemovalCondition& condition) : m_condition(condition)
         {
         }
      bool operator()(VHUtil::xml_tree::node* a)
         {
            return m_condition(a);
         }
   };

   int
   clear_string (std::string & s)
   {
      int total = 0;
      for (std::string::iterator it = s.begin(); it != s.end(); it ++) {
         * it = '\0';
         total += * it;
      }
      return total;
   }
}

namespace VHUtil {

std::ostream & operator << (std::ostream & o, const xml_tree::node &n)
{
   o << "<" << n.m_name;
   for (std::map< std::string, std::string >::iterator it
           = n.m_attributes.begin();
        it != n.m_attributes.end(); it ++)
      o << ' ' << throw_if_non_utf8((*it).first) << '='
        << '"' << throw_if_non_utf8((*it).second) << '"';
   o << ">";
   for (int i = 0; i < n.element_count(); i ++) {
      o << entityify(throw_if_non_utf8(n.characters_before_element(i)));
      o << * n.element(i);
   }
   o << entityify(throw_if_non_utf8(n.characters_before_element(n.element_count())));
   o << "</" << n.m_name << ">";
   return o;
}

std::ostream & operator << (std::ostream & o, const xml_tree & t)
{
   if (t.m_root)
      o << *(t.m_root);
   else
      o << "EMPTY TREE\n";
   return o;
}

xml_tree::xml_tree (const std::string & data, error_handling_mode error_mode)
   : m_root(0), m_phonyRoot(0), m_current_node_index(0)
{
   bool f_ok = true;
   xmlParserCtxtPtr pCtxt = 0;
   xmlDoValidityCheckingDefaultValue=1;

   try {
      pCtxt = xmlCreatePushParserCtxt(&m_SAXHandler, NULL, "", 0, 0);
      if (! pCtxt) {

         if (THROW == error_mode) {
            throw VH_exception ("XML_CTXT_ERROR");
         } else

         {
            VHUtil::cout() << "Unable to create parser ctxt." << std::endl;
            m_root = NULL;
            f_ok = false;
         }
      }

      if (f_ok) {
         m_ctx_assoc[pCtxt] = this;
         pCtxt->_private = this;

         int status = xmlParseChunk(pCtxt, data.c_str(), data.size(), 1);

         m_ctx_assoc.erase(m_ctx_assoc.find(pCtxt));

         if ((0 == status)
             && pCtxt->wellFormed) {
            ; // It's okay, don't report an error.
         } else {
            m_root = NULL;

            if (THROW == error_mode) {
               // Hack off trailing newlines so as not to confuse
               // downstream stuff
               std::string parse_error (m_xml_parse_error);
               while (parse_error.size ()) {
                  std::string::iterator i = parse_error.end () - 1;
                  if ('\n' == *i)
                     parse_error.erase (i);
                  else
                     break;
               }
               throw VH_exception ("XML_PARSE_ERROR", parse_error.c_str());
            }
            else
               VHUtil::cout() << "pCtxt->errNo is " << pCtxt->errNo << std::endl
                              << "libxml error is " << m_xml_parse_error << std::endl;
         }

      }
   } catch (...) {
      if ( pCtxt->myDoc )
         ::xmlFreeDoc(pCtxt->myDoc);
      xmlFreeParserCtxt(pCtxt);
      throw;
   }
   if ( pCtxt->myDoc ) {
      ::xmlFreeDoc(pCtxt->myDoc);
   }
   if (pCtxt)
      xmlFreeParserCtxt(pCtxt);
}

xml_tree::~xml_tree (void)
{
   if ( m_phonyRoot )
      delete m_phonyRoot;
   else if (m_root)
      delete m_root;
}

xml_tree::node::node (node * parent,
                      const std::string & name)
   :m_name(name), m_parent(parent)
{
}

xml_tree::node::node(const std::string & name, node *parent )
   :  m_name(name), m_parent(parent)
{
}

xml_tree::node::~node (void)
{
   for (std::vector< node * >::iterator it = m_elements.begin();
        it != m_elements.end(); it ++) {
      if (*it) delete *it;
   }
   // Clear out the character data, in case it had a secret in it.
   clear_string(m_characters);
   // Also clear out the attribute values.  The name of the element 
   // and the names of the attributes are not secrets, so don't 
   // worry about them.
   for (attribute_map::iterator mit = m_attributes.begin();
	 mit != m_attributes.end(); mit ++) {
      clear_string(mit->second);
   }
}

bool
xml_tree::node::remove (xml_tree::node * child)
{
   bool result = false;
   child_vector::iterator child_it;
   break_vector::iterator break_it;
   for (child_it = m_elements.begin(),break_it = m_character_breaks.begin();
        (child_it != m_elements.end()) && (child != * child_it);
        child_it ++,break_it ++)
      ;
   if (child == * child_it) {
      m_elements.erase(child_it);
      m_character_breaks.erase(break_it);
      result = true;
   }
   return result;
}

/*
* This is charmingly misnamed, because it really does the shallow part
* of a deep copy and then calls deep_copy_with_parent() to do the deep
* part.
*/
xml_tree::node *
xml_tree::node::deep_copy (void) const
{
   node * new_node = new node(m_name);

   new_node->m_characters = m_characters;
   new_node->m_character_breaks = m_character_breaks;
   new_node->m_attributes = m_attributes;

   for (child_vector::const_iterator it = m_elements.begin();
        it != m_elements.end(); it ++)
      new_node->m_elements.push_back((*it)->deep_copy_with_parent(new_node));
   return new_node;
}

xml_tree::node *
xml_tree::node::element (const std::string & name, int i)
{
   node * retval = NULL;
   for (std::vector< node * >::iterator it = m_elements.begin();
        it != m_elements.end(); it ++) {
      if ((* it)->m_name == name) {
         if (i --) {
            // A match, count it.
         } else {
            retval = * it;
            break;
         }
      }
   }
   return retval;
}

xml_tree::node *
xml_tree::node::element (const std::string & name,
                         const std::string & attrib,
                         const std::string & value,
                         int i)
{
   node * retval = NULL;
   for (std::vector< node * >::iterator it = m_elements.begin();
        it != m_elements.end(); it ++) {
      if (((* it)->m_name == name) && ((* it)->attribute(attrib) == value)) {
         if (i --) {
            // A match, count it.
         } else {
            retval = * it;
            break;
         }
      }
   }
   return retval;
}

xml_tree::node *
xml_tree::node::element (const std::string & name,
                         const std::string & attrib1,
                         const std::string & value1,
                         const std::string & attrib2,
                         const std::string & value2,
                         int i)
{
   node * retval = NULL;
   for (std::vector< node * >::iterator it = m_elements.begin();
        it != m_elements.end(); it ++) {
      if (((* it)->m_name == name)
          && ((* it)->attribute(attrib1) == value1)
          && ((* it)->attribute(attrib2) == value2)) {
         if (i --) {
            // A match, count it.
         } else {
            retval = * it;
            break;
         }
      }
   }
   return retval;
}

xml_tree::node *
xml_tree::node::e (unsigned int i)
{
   node * n = element(i);
   if (!n)
      throw VH_exception ("XML_NO_ELEMENT");
   return n;
}

xml_tree::node *
xml_tree::node::e (const std::string & name,
                   int i)
{
   node * n = element(name, i);
   if (!n)
      throw VH_exception ("XML_NO_ELEMENT");
   return n;
}

xml_tree::node *
xml_tree::node::e (const std::string & name,
                   const std::string & attrib,
                   const std::string & value,
                   int i)
{
   node * n = element(name, attrib, value, i);
   if (!n)
      throw VH_exception ("XML_NO_ELEMENT");
   return n;
}

xml_tree::node *
xml_tree::node::e (const std::string & name,
                   const std::string & attrib1,
                   const std::string & value1,
                   const std::string & attrib2,
                   const std::string & value2,
                   int i)
{
   node * n = element(name, attrib1, value1, attrib2, value2, i);
   if (!n)
      throw VH_exception ("XML_NO_ELEMENT");
   return n;
}

int
xml_tree::node::element_index (const node * n) const
{
   unsigned int i;
   for (i = 0; i < m_elements.size(); i ++) {
      if (m_elements[i] == n)
         break;
   }
   if (i == m_elements.size()) {
      i = static_cast<unsigned int>(-1);
   }
   return i;
}

std::string
xml_tree::node::characters_before_element (unsigned int i) const
{
   unsigned int i_start = (i == 0) ? 0 : m_character_breaks[i - 1];
   return m_characters.substr(i_start,
                              (i == m_character_breaks.size())
                              ? std::string::npos
                              : m_character_breaks[i] - i_start);
}

void
xml_tree::start_document_handler (void * ctx)
{
   xml_tree & self = from_ctx(ctx);
   self.current() = self.m_phonyRoot=self.m_root = new node(NULL, "DOCUMENT_ROOT");
}

/*
* Removes the bogus root node that was created by
* start_document_handler.
*/
void
xml_tree::end_document_handler (void * ctx)
{
   xml_tree & self = from_ctx(ctx);
   if (self.m_root) {
      self.m_root = self.m_root->element(0);
   }
}

void
xml_tree::start_element_handler (void * ctx, const xmlChar * name,
                                 const xmlChar ** atts)
{
   xml_tree & self = from_ctx(ctx);
   node * newnode
      = new node(self.current(),
                 reinterpret_cast< const char * >(name));
   self.current()->add_element(newnode);
   self.m_current_node_index ++;
   self.current() = newnode;
   if (atts) {
      for (int i = 0; atts[i] != NULL; i += 2) {
         self.current()
            ->add_attribute(reinterpret_cast< const char * >(atts[i]),
                            reinterpret_cast< const char * >(atts[i + 1]));
      }
   }
}

/*
* 'Pops' the top node off the 'stack', returning to the lexically
* enclosing one, since the XML parser tells us that we are done with
* the one we were working in.
*
*/
void
xml_tree::end_element_handler (void * ctx, const xmlChar * name)
{
   xml_tree & self = from_ctx(ctx);
   self.m_current_node_index --;
}

/*
* The XML parser tells us that we have characters, so remember them
* somewhere.  They might be useful later.
*/
void
xml_tree::characters_handler (void * ctx, const xmlChar * ch, int len)
{
   xml_tree & self = from_ctx(ctx);

   self.current()
      ->add_characters(std::string(reinterpret_cast< const char * >(ch),
                                   len));
}

void
xml_tree::cdata_handler (void * ctx, const xmlChar * ch, int len)
{
   characters_handler(ctx, ch, len);
}

void
xml_tree::error_handler (void * ctx, const char * ch, ...)
{
   xml_tree & self = from_ctx(ctx);
   va_list ap;
   va_start(ap, ch);
   char buf[1024];
   vsprintf(buf, ch, ap);
   va_end(ap);
   self.m_xml_parse_error = "XMLLIB ERROR: ";
   self.m_xml_parse_error += buf;

}

void
xml_tree::warning_handler (void * ctx, const char * ch, ...)
{
   xml_tree & self = from_ctx(ctx);
   va_list ap;
   va_start(ap, ch);
   char buf[1024];
   vsprintf(buf, ch, ap);
   va_end(ap);
   self.m_xml_parse_error = "XMLLIB WARNING: ";
   self.m_xml_parse_error += buf;

}

void xml_tree::node::sort_children(compare_fn f)
{
   std::sort (this->m_elements.begin (), this->m_elements.end   (), f);
}

void xml_tree::node::remove_children_if(if_fn f)
{
   typedef std::vector<node*> NodeVector_t;

   NodeVector_t newElements;

   std::remove_copy_if(m_elements.begin(),m_elements.end(),std::back_insert_iterator<NodeVector_t>(newElements),f);

   m_elements.swap(newElements);

   for(NodeVector_t::iterator ii=newElements.begin(); ii!=newElements.end(); ++ii)
   {
      if ( f(*ii) )
         delete *ii;
   }
}

void xml_tree::node::remove_children_if(NodeRemovalCondition& condition)
{
   typedef std::vector<node*> NodeVector_t;

   NodeVector_t newElements;

   RemovalPredicate predicate(condition);

   std::remove_copy_if(m_elements.begin(),m_elements.end(),std::back_insert_iterator<NodeVector_t>(newElements),predicate);

   m_elements.swap(newElements);

   for(NodeVector_t::iterator ii=newElements.begin(); ii!=newElements.end(); ++ii)
   {
      if ( condition.RemoveIt(*ii) )
         delete *ii;
   }

}

xmlSAXHandler xml_tree::m_SAXHandler = {
   NULL, /* internalSubset */
   NULL, /* isStandalone */
   NULL, /* hasInternalSubset */
   NULL, /* hasExternalSubset */
   NULL, /* resolveEntity */
   NULL, /* getEntity */
   NULL, /* entityDecl */
   NULL, /* notationDecl */
   NULL, /* attributeDecl */
   NULL, /* elementDecl */
   NULL, /* unparsedEntityDecl */
   NULL, /* setDocumentLocator */
   xml_tree::start_document_handler, /* startDocument */
   xml_tree::end_document_handler, /* endDocument */
   xml_tree::start_element_handler, /* startElement */
   xml_tree::end_element_handler, /* endElement */
   NULL, /* reference */
   xml_tree::characters_handler, /* characters */
   NULL, /* ignorableWhitespace */
   NULL, /* processingInstruction */
   NULL, /* comment */
   xml_tree::warning_handler, /* xmlParserWarning */
   xml_tree::error_handler, /* xmlParserError */
   NULL, /* xmlParserError */
   NULL, /* getParameterEntity */
   xml_tree::cdata_handler, /* cdataBlock; */
};

std::map< void *, xml_tree * > xml_tree::m_ctx_assoc;

template<class T>
T get_attribute_value_as(const VHUtil::xml_tree::node* node, const std::string& attribName)
{
   const std::string lStr=node->attribute(attribName);

   T l;

   std::istringstream iss(lStr);
   iss >>l;

   if ( !iss )
      throw VH_exception ("XML_BAD_ATTRIBUTE_TYPE", attribName.c_str(),lStr.c_str());

   return l;
}

template long get_attribute_value_as<long>(const VHUtil::xml_tree::node* node, const std::string& attribName);
template unsigned get_attribute_value_as<unsigned>(const VHUtil::xml_tree::node* node, const std::string& attribName);
template int get_attribute_value_as<int>(const VHUtil::xml_tree::node* node, const std::string& attribName);

template<class T>
void add_attribute_from(VHUtil::xml_tree::node* node, const std::string& attribName, const T& value)
{
   std::ostringstream oss;

   oss << value;

   const std::string valueStr=oss.str();

   node->add_attribute(attribName,valueStr);
}

template void add_attribute_from<int>(VHUtil::xml_tree::node*, const std::string& ,const int&);
template void add_attribute_from<long>(VHUtil::xml_tree::node*, const std::string& ,const long&);

}

void VHUtil::PrintNode(std::ostream& os, const xml_node & n)
{
   os <<n;
}
