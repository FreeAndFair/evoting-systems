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
#if defined (_MSC_VER)
# pragma warning (disable: 4786)
#endif

#include <support/random_internal.cpp>
extern "C" {
#include <misc/cutest.h>
}
#include "support_test.h"

namespace {
   std::string xml_2_str (const VHUtil::xml_tree &tree)
   {
      std::ostringstream tmp;
      tmp << tree;
      return (tmp.str ());
   }
   
   RandomState
   friendly_generate_random_state (const std::string &key)
   {
      RandomState return_value = 0;
      VHUtil::xml_tree rs_key ("<" RANDOM_SEED_KEY "/>");
      rs_key.root ()->add_characters (key);

      VH_propagate (VHTI_generate_random_state(xml_2_str (rs_key).c_str (),
                                               &return_value),
                    YEAH_YEAH_WHATEVER);
      return return_value;
   }
   
   VHInternal::RS *
   rs_from_key (const std::string &key_text,
                std::string * initial_xml = 0)
   {
      auto_freeing<RandomState> init_state (friendly_generate_random_state (key_text));

      VHUtil::xml_tree tree (static_cast<char *>(init_state));

      if (initial_xml)
         *initial_xml = xml_2_str (tree);

      return new VHInternal::RS (xml_2_str (tree));
   }
}

void
RS_class (CuTest *tc)
{
   bool fCaughtException = false;

   try {
      std::auto_ptr<VHInternal::RS> rs  (rs_from_key ("How now brown cow"));
      {
         // Every time we call get_bits, the output should be different.
   
         std::string last_bits (rs->get_bits (20));

         for (int i = 0;
              i < 10;
              i++) {
            auto_freeing<const char *> current_bits(rs->get_bits (20));

            CuAssert (tc,
                      "1: Current bits doesn't differ from last bits",
                      strcmp (current_bits, last_bits.c_str ()));

            last_bits = current_bits;
         }
      }

      // A new RS, upon which we've never called get_bits, should
      // return the argument to the ctor when we cast it to a
      // RandomState.

      {
         std::string virgin_xml;
         std::auto_ptr<VHInternal::RS> rs (rs_from_key ("", &virgin_xml));
         const std::string current_state (static_cast<RandomState>(*rs));

         if (!(virgin_xml == current_state)) {
            std::ostringstream whine;
            whine << "current state `"
                  << current_state
                  << "' doesn't match that passed to ctor `"
                  << virgin_xml
                  << "'"
                  << std::endl;
            CuAssert (tc,
                      (char *) whine.str ().c_str (),
                      virgin_xml == current_state);
         }

         // But of course, if we consume bits, then get the state
         // again, it will have changed.
         rs->get_bits (20);
         CuAssert (tc,
                   "2: Current random state doesn't differ from last random state",
                   virgin_xml != static_cast<RandomState>(*rs));
      }

      // If I create two of 'em, with different initial keys, they
      // should return different bits.
      {
         std::auto_ptr<VHInternal::RS> dog (rs_from_key ("Rover.  Woof woof."));
         std::auto_ptr<VHInternal::RS> cat (rs_from_key ("Meow.  Feed me."));
         const std::string dog_state = dog->get_bits (20);
         const std::string cat_state = cat->get_bits (20);
         if (!(dog_state != cat_state))
         {
            std::ostringstream whine;
            whine << "States didn't differ: both were `"
                  << dog_state
                  << "'";
            CuAssert (tc,
                      (char *) whine.str ().c_str (),
                      dog_state != cat_state);
         }
      }

      {
         // operator RandomState * returns a pointer whose referent we
         // are expected to modify: we set it to the return value from
         // VHTI_dup, and write into that buffer a RandomState XML
         // string.  Then our next call to get_bits will return bits
         // from that very state.  If we then immediately call
         // get_bits again, we naturally will get different bits.
         // Thus we will be able to pass an RS object to functions
         // that are expecting a RandomState and a RandomState *, and
         // it will do The Right Thing.

         auto_freeing <RandomState> second (friendly_generate_random_state ("I am the second Random State."));
         std::auto_ptr<VHInternal::RS> rs (rs_from_key (""));
         RandomState *p = *rs;
         *p = VHTI_dup (second);
         RandomState actual = *rs;

         {
            std::ostringstream whine;
            whine << "Expected: "
                  << std::endl
                  << static_cast<const char *>(second)
                  << "but got : "
                  << std::endl
                  << static_cast<const char *>(actual)
                  << std::endl;
            CuAssert (tc,
                      const_cast<char *>(whine.str ().c_str ()),
                      0 == strcmp (actual, second));
         }

         rs->get_bits (1);
         actual = *rs;

         {
            std::ostringstream whine;
            whine << "Expected anything except: "
                  << static_cast<const char *>(second)
                  << std::endl;
            CuAssert (tc,
                      const_cast<char *>(whine.str ().c_str ()),
                      0 != strcmp (actual, second));
         }
      }

      // It's perfectly OK to make an RS from an empty string.
      std::auto_ptr<VHInternal::RS> norbert (rs_from_key (""));
      VHUtil::xml_tree actual (static_cast<RandomState>(*norbert));

      CuAssert (tc, 
                "unexpected hash value",

                // this may look like an arbitrary number, but it
                // isn't; it's the decimal version of the SHA1 hash of
                // the empty string.  See for yourself with this
                // little Bash-and-Perl magic:

                // (echo -n 0x; (echo -n | openssl sha1)) | perl -MMath::BigInt -n -e 'print Math::BigInt->new ($_)'; echo

                "1245845410931227995499360226027473197403882391305" == actual.root ()->e (RANDOM_BLOCK)->characters () );
   }
   catch (VHUtil::Exception &e)
   {
      fCaughtException = true;
      std::cerr << "I must say, I wasn't expecting the Spanish Inquisition."
                << std::endl
                << e.what ()
                << std::endl;
   }

   CuAssert (tc, "Oops.  Caught an exception.", !fCaughtException);
}
