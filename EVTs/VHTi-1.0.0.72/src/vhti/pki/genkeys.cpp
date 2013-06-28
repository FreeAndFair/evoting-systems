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

#include "vhti/genkeys.h"
#include <support/bignum.h>
#include <support/internal_error.h>
#include <misc/vh_excpt.h>
#include <misc/array.h>

#include <openssl/rsa.h>
#include <openssl/dsa.h>
#include <openssl/pem.h>
#include <openssl/err.h>
#include <openssl/evp.h>

#include <string>
#include <sstream>
#include <cassert>
#include "misc.h"

// FIPS 186 says this should be between 512 and 1024 inclusive, and a
// multiple of 64
const unsigned int DEFBITS = 1024;

enum keytype { PUBLIC, PRIVATE };

namespace {
   
   std::string
      key_to_xml_string (const keytype type,
      const char *const tagname,
      RSA *rsa,    // exactly one of rsa and dsa must be 0
      DSA *dsa)
   {
      std::string rv;
      
      auto_BIO bio (BIO_new (BIO_s_mem ()));
      if (bio)
      {
         int status = -1;
         if (dsa)
         {
            assert (!rsa);
            switch (type)
            {
            case PUBLIC:
               status = PEM_write_bio_DSA_PUBKEY (bio,
                  dsa);
               break;
            case PRIVATE:
               status = PEM_write_bio_DSAPrivateKey (bio,
                  dsa,
                  NULL,
                  NULL,
                  0,
                  0,
                  NULL);
               break;
            }
         }
         else
         {
            assert (!dsa);
            switch (type)
            {
            case PUBLIC:
               status = PEM_write_bio_RSA_PUBKEY (bio, // PKCS#1 format
                  rsa);
               break;
            case PRIVATE:
               status = PEM_write_bio_RSAPrivateKey (bio,
                  rsa,
                  NULL,
                  NULL,
                  0,
                  NULL,
                  NULL);
               break;
            }
         }
         if ((1 == status)
            &&
            (1 == BIO_flush (bio)))
         {
            int PEM_length = BIO_pending (bio);
            VHUtil::array<unsigned char> PEM (PEM_length + 1);
            
            if (BIO_read (bio, PEM, PEM_length) > 1)
            {
               PEM [PEM_length] = '\0';
               
               std::ostringstream tmp;
               tmp << "<" << tagname << ">"
                  << PEM
                  << "</" << tagname << ">" << std::endl;
               rv.assign (tmp.str ());
            }
         }
      }
      
      if (!rv.length ())
      {
         throw SSL_ERROR;
      }
      
      return rv;
   }
   
   void
      make_signing_keypair (std::string &Private,
      std::string &Public)
   {
      bool succeeded = false;
      DSA *dsa_params = DSA_generate_parameters (DEFBITS, /* bits */
         NULL, /* seed */
         0, /* seed length */
         NULL, /* counter_ret */
         NULL, /* h_ret */
         NULL, /* callback */
         NULL /* callback arg */
         );
      
      if (dsa_params)
      {
         if (DSA_generate_key (dsa_params))
         {
            Private = key_to_xml_string (PRIVATE,
               SIGNING_PRIVATE_KEY,
               0,
               dsa_params);
            Public = key_to_xml_string (PUBLIC,
               SIGNING_PUBLIC_KEY,
               0,
               dsa_params);
            succeeded = true;
         }
         DSA_free (dsa_params);
      }
      if (!succeeded)
         throw SSL_ERROR;
   }
   
   void
      make_encryption_keypair (std::string &Private,
      std::string &Public)
   {
      bool succeeded = false;
      RSA *rsa = RSA_generate_key (DEFBITS, /* bits */
         3, /* public exponent */
         NULL, /* callback */
         NULL /* callback arg */
         );
      
      if (rsa)
      {
         Private = key_to_xml_string (PRIVATE,
            ENCRYPTION_PRIVATE_KEY,
            rsa,
            0);
         Public = key_to_xml_string (PUBLIC,
            ENCRYPTION_PUBLIC_KEY,
            rsa,
            0);
         succeeded = true;
         
         RSA_free (rsa);
      }
      if (!succeeded)
         throw SSL_ERROR;
   }
}

int
VHTI_generate_keys(IdentInfo ident_info,
                   GeneralPurposePrivateKey *pr,
                   GeneralPurposePublicKey  *pu)
{
   int result = 0;
   
   try
   {
      if (::VHTI_validate (IDENT_INFO, ident_info))
         throw XML_ERROR (ident_info);
      
      std::string ER_xml;
      std::string EU_xml;
      std::string SR_xml;
      std::string SU_xml;
      
      make_encryption_keypair (ER_xml, EU_xml);
      make_signing_keypair (SR_xml, SU_xml);
      
      VHUtil::xml_tree pub  ("<" GENERAL_PURPOSE_PUBLIC_KEY  "/>");
      pub.root ()->add_element (VHUtil::xml_tree (ident_info).root()->
         deep_copy ());
      pub.root ()->add_element (VHUtil::xml_tree (SU_xml    ).root()->
         deep_copy ()); 
      pub.root ()->add_element (VHUtil::xml_tree (EU_xml    ).root()->
         deep_copy ());
      
      VHUtil::xml_tree priv ("<" GENERAL_PURPOSE_PRIVATE_KEY "/>");
      priv.root ()->add_element (VHUtil::xml_tree (ident_info).root()->
         deep_copy ());
      priv.root ()->add_element (VHUtil::xml_tree (SR_xml    ).root()->
         deep_copy ()); 
      priv.root ()->add_element (VHUtil::xml_tree (ER_xml    ).root()->
         deep_copy ());
      
      {
         std::ostringstream pubstream;
         pubstream << *(pub.root ());
         *pu = VHTI_dup (pubstream.str ().c_str ());
      }
      {
         std::ostringstream privstream;
         privstream << *(priv.root ());
         *pr = VHTI_dup (privstream.str ().c_str ());
      }
   }
   catch (const VHUtil::Exception & e)
   {
      VHTI_set_last_error(e);
      VHUtil::cout() << e.what () << std::endl;
      result = e.getResultNo();
   }
   return result;
}
