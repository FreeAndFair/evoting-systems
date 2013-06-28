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
#pragma warning(disable: 4786)
#include <misc/vh_excpt.h>
#include <misc/xml_tree.h>
#include "./sanity.h"
#include "./bignum.h"
#include <set>
#include <string>

namespace {
template<class T>class no_dups {
private:
   std::set<T> _s;
public:
   std::pair<std::set<T>::iterator, bool> 
   insert (const T&datum, const std::string &message)
      {
         if (_s.find (datum) != _s.end ())
            VHUtil::_check (message.c_str (), __FILE__, __LINE__);

         return _s.insert (datum);
      }
};
}

namespace VHInternal {

void
sanity_check_blank_ballot (VHUtil::xml_node bb)
{
   no_dups<std::string> question_refs_seen;
   no_dups<std::string> answer_refs_seen;

   VHUtil::xml_node current_question = 0;
   for (int i=0;
        current_question = bb->element(BALLOT_QUESTION, i);
        i++)
   {
      question_refs_seen.insert (current_question->attribute(QUESTION_REFERENCE), "DUPLICATE_QUESTION_REF");

      no_dups<auto_BN>     answer_marks_seen;

      VHUtil::xml_node current_ans = 0;
      for (int j=0;
           current_ans = current_question->element(BALLOT_ANSWER, j);
           j++)
      {
         answer_refs_seen.insert (current_ans->attribute (ANSWER_REFERENCE), "DUPLICATE_ANSWER_REF");
         answer_marks_seen.insert (xml2BN(current_ans->e(ANSWER_MARK)), "DUPLICATE_ANSWER_MARK");
      }
   }
}
}
