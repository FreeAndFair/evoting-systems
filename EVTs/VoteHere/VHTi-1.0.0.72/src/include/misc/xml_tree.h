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

#ifndef _UTIL_XML_TREE_HPP
#define _UTIL_XML_TREE_HPP
#pragma warning(disable: 4786)

#include <iosfwd>
#include <map>
#include <vector>
#include <string>
#include <sstream>

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

namespace VHUtil {
class NodeRemovalCondition;

class xml_tree
{
public:
   enum error_handling_mode { THROW, NO_THROW };
   xml_tree(const std::string & data, error_handling_mode mode = THROW);
   ~xml_tree(void);

   bool parsed_OK (void)
      {
         return m_root != NULL;
      }

   std::string get_dtd_public_id(void) const
      {
         return m_dtd_public_id;
      }

   operator std::string () const
   {
      std::ostringstream tmp;
      tmp << *this;
      return tmp.str ();
   } 

   // Same as the above, but easier to type.
   std::string str () const
   {
      return static_cast<std::string>(*this);
   }

   class node
   {
   public:
      node(node * parent, const std::string & name);
      node(const std::string & name, node *parent = NULL);
      node(void)
         {}
      ~node(void);

      void set_name(const std::string & s)
         {
            m_name = s;
         }

      void add_element(node * e)
         {
            e->m_parent = this;
            m_character_breaks.push_back(m_characters.size());
            m_elements.push_back(e);
         }

      node * new_element(const std::string & name, node * parent = 0 )
         {
            node *new_e = new node;
            new_e->m_name = name;
            new_e->m_parent =parent;
            add_element(new_e);
            return new_e;
         }

      void erase(void)
         {
            if (m_parent)
            {
               m_parent->remove
                  (this);
               delete this;
            }
         }

      bool remove
      (node * child);

      node * deep_copy(void) const;

   private:

      node * deep_copy_with_parent(node * new_parent) const
         {
            node * new_node = deep_copy();
            new_node->m_parent = new_parent;
            return new_node;
         }

   public:

      const std::map< std::string, std::string > attributes () const
         {
            return m_attributes;
         }

      void add_attribute(const std::string & n,
                         const std::string & v)
         {
            m_attributes[n] = v;
         }

      void remove_attribute(const std::string & n)
         {
            std::map< std::string, std::string >::iterator it;
            it = m_attributes.find(n);
            if (it != m_attributes.end())
               m_attributes.erase(it);
         }

      void add_characters(const std::string & s)
         {
            m_characters += s;
         }

      void erase_all_characters(void)
         {
            m_characters = "";
            for (std::vector< int >::iterator it = m_character_breaks.begin();
                 it != m_character_breaks.end(); it++)
            {
               *it=0;
            }
         }

      const std::string & name(void) const
         {
            return m_name;
         }

      node * element(unsigned int i)
         {
            return i < m_elements.size()
               ? m_elements[i] : NULL;
         }

      const node * element(unsigned int i) const
         {
            return i < m_elements.size()
               ? m_elements[i] : NULL;
         }

      node * element(const std::string & name, int i = 0);
      node * element(const std::string & name,
                     const std::string & attrib,
                     const std::string & value, int i = 0);
      node * element(const std::string & name,
                     const std::string & attrib1,
                     const std::string & value1,
                     const std::string & attrib2,
                     const std::string & value2, int i = 0);
      int element_index(const node * n) const;

      node * e(unsigned int i);
      node * e(const std::string & name, int i = 0);
      node * e(const std::string & name,
               const std::string & attrib,
               const std::string & value, int i = 0);
      node * e(const std::string & name,
               const std::string & attrib1,
               const std::string & value1,
               const std::string & attrib2,
               const std::string & value2, int i = 0);

      const std::string & attribute(const std::string & name) const
         {
            return m_attributes[name];
         }

      bool has_attribute(const std::string & name)
         {
            return m_attributes.find(name) != m_attributes.end();
         }

      const std::string & characters(void) const
         {
            return m_characters;
         };

      std::string characters_before_element(const node * n) const
         {
            int index = element_index(n);
            std::string chars;
            if (index != -1)
            {
               chars=characters_before_element(index);
            }
            return chars;
         }

      std::string characters_before_element(unsigned int i) const;

      operator std::string () const
         {
            std::ostringstream tmp;
            tmp << *this;
            return tmp.str ();
         } 

      // Same as the above, but easier to type.
      std::string str () const
         {
            return static_cast<std::string>(*this);
         }

      node * parent(void)
         {
            return m_parent;
         }

      int element_count(void) const
         {
            return m_elements.size();
         }

      typedef bool (*compare_fn) (const node *a,
                                  const node *b);
      void sort_children(compare_fn f);

      typedef bool (*if_fn) (const node* );
      void remove_children_if(if_fn f);

      void remove_children_if(NodeRemovalCondition& condition);
   private:
      typedef std::vector< int > break_vector;
      typedef std::vector< node * > child_vector;
      typedef std::map< std::string, std::string > attribute_map;
      std::string m_name;
      std::string m_characters;
      break_vector m_character_breaks;
      node * m_parent;
      child_vector m_elements;
      mutable attribute_map m_attributes;

      node(const node&);
      node& operator=(const node&);

      friend std::ostream & operator <<(std::ostream & o, const node &n);
   };

   static void start_document_handler(void * ctx);
   static void end_document_handler(void * ctx);
   static void start_element_handler(void * ctx, const xmlChar * name,
                                     const xmlChar ** atts);
   static void end_element_handler(void * ctx, const xmlChar * name);
   static void xml_tree::reference_handler (void * ctx, const xmlChar * name);
   static void characters_handler(void * ctx, const xmlChar * ch, int len);
   static void cdata_handler(void * ctx, const xmlChar * ch, int len);
   static void error_handler(void * ctx, const char * ch, ...);
   static void warning_handler(void * ctx, const char * ch, ...);

   node * root(void)
      {
         return m_root;
      }
   const node * root(void) const
      {
         return m_root;
      }
private:

   static xml_tree & from_ctx(void * ctx)
      {
         return * m_ctx_assoc[ctx];
      }

   node * & current(void)
      {
         if (m_current_node_index >= static_cast< int >(m_node_stack.size()))
            m_node_stack.push_back(NULL);
         return m_node_stack[m_current_node_index];
      }

protected:
   node * m_root;
private:
   node * m_phonyRoot;

   std::vector< node * > m_node_stack;
   int m_current_node_index;

   static xmlSAXHandler m_SAXHandler;
   static std::map< void *, xml_tree * > m_ctx_assoc;

   xml_tree(const xml_tree&);
   xml_tree& operator=(const xml_tree&);

   std::string m_xml_parse_error;

   std::string m_dtd_public_id;
   friend std::ostream & operator <<(std::ostream & o, const xml_tree & n);
};

typedef xml_tree::node * xml_node;

void PrintNode(std::ostream& os, const xml_node & n);

class NodeRemovalCondition
{
public:
   virtual bool RemoveIt(xml_tree::node* )=0;
   bool operator()(xml_tree::node* a)
      {
         return RemoveIt(a);
      }
};

int UTF8Toisolat1(unsigned char* out, int *outlen,
                  const unsigned char* in, int *inlen);
int isolat1ToUTF8(unsigned char* out, int *outlen, const unsigned char* in, int *inlen);

std::string characters_8859_1_transcoder(const char *ch, int len, int *res);
std::string characters_8859_1_transcoder(const char *ch, int *res);

template<class T>
T get_attribute_value_as(const VHUtil::xml_tree::node* node, const std::string& attribName);

template<class T>
void add_attribute_from(VHUtil::xml_tree::node* node, const std::string& attribName, const T& value);

}

#endif

