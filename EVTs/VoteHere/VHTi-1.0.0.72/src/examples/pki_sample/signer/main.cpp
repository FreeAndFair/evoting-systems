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

// Helper program to make a DSA signature.  It's surprising that the
// `openssl' program doesn't provide this feature.
#include <vhti/genkeys.h>
#include <vhti/crypt.h>
#include <vhti/sign.h>
#include <misc/vh_excpt.h>
#include <misc/file_contents.h>

#include <libxml/tree.h>

#include <ctime>
#include <string>
#include <cstring>
#include <iostream>
#include <sstream>
#include <fstream>
#include <io.h>
#include <cerrno>

namespace {

const std::string pubkey_fn = "pubkey.xml";
const std::string prvkey_fn = "prvkey.xml";

inline bool
file_missing (const std::string &fn)
{
   return ((-1 == _access (fn.c_str (), 04)) // 04: readable
           &&
           (ENOENT == errno));
}

std::string
make_C_string_constant (const std::basic_string<unsigned char> &stuff)
{
   std::ostringstream result;
   result << '\"';
   int chars_this_line = 0;
   for (std::string::size_type i = 0;
        i < stuff.size ();
        i++)
   {
      const unsigned char ch = stuff[i];
      switch (ch)
      {
      case '\n':
         // Insert line break for tidiness
         result << "\\n\"\n\"";
         break;

      case '\t': result << "\\t"; break;
      case '\v': result << "\\v"; break;
      case '\b': result << "\\b"; break;
      case '\r': result << "\\r"; break;
      case '\f': result << "\\f"; break;
      case '\a': result << "\\a"; break;

      case '\\':
      case '\"':
         result << '\\'
                <<  ch;
         break;
      default:
         if (isprint (ch))
            result <<  ch;
         else
         {
            char octal[4];
            sprintf (octal, "%03.3o",  ch);
            result << '\\'
                   << octal;
         }
         break;
      }
   }

   result << '"';
   return result.str ();
}

std::string
current_time_string ()
{
   time_t now = time (0);
   std::string return_value = ctime (&now);
   return_value.erase (return_value.size () - 1); // nuke trailing newline
   return return_value;
}

int
maybe_generate_keys ()
{
   int result = 0;
                
   if (file_missing (pubkey_fn)
       &&
       file_missing (prvkey_fn))
   {
      if (!result)
      {
         auto_freeing<GeneralPurposePrivateKey>    SigPrvkey = 0;
         auto_freeing<GeneralPurposePublicKey>     SigPubkey = 0;
   
         std::ostringstream ident_info;
         ident_info << "<IdentInfo>"
                    << current_time_string ()
                    << "</IdentInfo>";
         result = VHTI_generate_keys(ident_info.str ().c_str (),
                                     &SigPrvkey,
                                     &SigPubkey);
         if (!result)
         {
            std::ofstream pubstream (pubkey_fn.c_str ());
            std::ofstream prvstream (prvkey_fn.c_str ());

            if (pubstream && prvstream)
            {
               pubstream << (const char *)SigPubkey;
               prvstream << (const char *)SigPrvkey;
            }
            else
            {
               std::cerr << ::_strerror ("Creating file: ");
               result = -2;
            }
         }
         else
         {
            std::cerr << "VHTI_generate_keys failed with result "
                      << result
                      << std::endl;
            exit(1);

         }
      }
   }
   return result;
}

}

int
main (int argc, char *argv[])
{
   int result = 0;

#if 0
   // Test make_C_string_constant on all possible bytes
   {
      unsigned char all_bytes[256];
      for (unsigned int i = 0;
           i < sizeof (all_bytes);
           i++)
      {
         all_bytes[i] = (unsigned char) (i);
      }

      {
         std::basic_string<unsigned char> tmp;
         tmp.assign (all_bytes, sizeof (all_bytes));
         std::cout << make_C_string_constant (tmp)
                   << std::endl;
      }
      exit (0);
   }
#endif

   try
   {
      result = maybe_generate_keys ();

      if (!result)
      {
         std::string pub (VHUtil::file_contents (pubkey_fn.c_str ()));
         std::string prv (VHUtil::file_contents (prvkey_fn.c_str ()));

         auto_freeing<Signature> signature = 0;
         std::basic_string<unsigned char>  text;

         {
            const size_t buffer_chars = 100;
            char buf [buffer_chars];
            std::cin.read (buf, buffer_chars);
            while (std::cin.gcount ())
            {
               text.append ((unsigned char *) buf, std::cin.gcount ());
               std::cin.read (buf, buffer_chars);
            }
         }

         result = VHTI_sign(prv.c_str (),
                            (const char *) text.c_str(),
                            &signature);

         if (!result)
         {
            auto_freeing<CheckResults> c_res = 0;
            // Might's well ensure that it verifies too
            result = VHTI_verify_signature (pub.c_str (),
                                            (const char *)text.c_str (),
                                            signature,
                                            &c_res);

            if (!result)
            {
               if (::strstr (c_res, CHECK_SUCCESS_TEXT))
               {
                  std::cerr << "(whew -- the signature that we just made is OK: "
                            << (const char *) c_res
                            << ")"
                            << std::endl;

                  std::cout << "Public key:"
                            << std::endl
                            << make_C_string_constant ((unsigned char *) pub.c_str ())
                            << std::endl
                            << "Private key:"
                            << std::endl
                            << make_C_string_constant ((unsigned char *) prv.c_str ())
                            << std::endl
                            << "Cleartext: "
                            << std::endl
                            << make_C_string_constant (text)
                            << std::endl
                            << "Signature:"
                            << std::endl
                            << (const char *) signature
                            << std::endl;
               }
               else
               {
                  std::cerr << "Bizarre.  The signature that we just made didn't verify."
                            << std::endl;
               }
            }
            else
            {
               std::cerr << "VHTI_verify aborted with result "
                         << result
                         << std::endl;
            }
         }
         else
         {
            std::cerr << "Signing failed with result "
                      << result
                      << std::endl;
         }
      }
      else
      {
         std::cerr << "maybe_generate_keys failed with result "
                   << result
                   << std::endl;
      }
   }
   catch (const VHUtil::Exception & e)
   {
      result = e.getResultNo();
      std::cerr << "Caught exception: "
                << e.what ()
                << std::endl;
   }

   return result;
}
