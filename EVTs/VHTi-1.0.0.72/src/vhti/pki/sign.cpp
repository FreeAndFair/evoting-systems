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

#include "vhti/sign.h"
#include "./pki_internal.h"
#include <support/internal_error.h>
#include <misc/array.h>
#include <misc/vh_excpt.h>
#include <misc/vh_cout.h>
#include <misc/xml_tree.h>
#include <misc/safe_xml_tree.h>

#include <openssl/dsa.h>
#include <openssl/err.h>
#include <openssl/evp.h>
#include <openssl/pem.h>

#include <string>
#include <sstream>

#include "misc.h"

namespace {
   
   class free_DSA {
   public:
      static void free(DSA *x)
      {
         DSA_free(x);
      }
   };
   typedef auto_C_PTR<DSA, free_DSA> auto_DSA;
   
   class free_DSA_SIG {
   public:
      static void free(DSA_SIG *x)
      {
         DSA_SIG_free(x);
      }
   };
   typedef auto_C_PTR<DSA_SIG, free_DSA_SIG> auto_DSA_SIG;

   /* call `DSA_free' on the return value (which will never be NULL) */
   DSA *
      DSA_from_xml (const ustring &xml,
      const bool public_only)
   {
      DSA *rv = 0;
      VHUtil::xml_tree xt ((const char *) xml.c_str ());
      std::string pem_encoded = xt.root()->e (public_only
         ? SIGNING_PUBLIC_KEY
         : SIGNING_PRIVATE_KEY)->characters ();
      
      auto_BIO mem (BIO_new (BIO_s_mem ()));
      if (!mem)
         throw SSL_ERROR;
      
      if ((BIO_write (mem,
         pem_encoded.data (),
         pem_encoded.size ()) <= 0)
         ||
         (1 != BIO_flush (mem)))
         throw SSL_ERROR;
      
      if (public_only)
      {
         rv = PEM_read_bio_DSA_PUBKEY (mem,
            NULL,
            NULL,
            NULL);
      }
      else
      {
         rv = PEM_read_bio_DSAPrivateKey (mem,
            NULL,
            NULL,
            NULL);
      }
      
      VH_nonzero (rv,
                  DSA_KEY_PARSING_ERROR);

      return (rv);
   }

   // Throws exception on failure
   ustring
      make_digest (const ustring &message)
   {
      bool succeeded = false;
      
      ustring rv;
      EVP_MD_CTX mdctx;
      
      EVP_MD_CTX_init(&mdctx);
      if ((1 == EVP_DigestInit_ex(&mdctx, EVP_sha1(), NULL))
          &&
          (1 == EVP_DigestUpdate(&mdctx,
                                 message.data (),
                                 message.size())))
      {
         VHUtil::array<unsigned char> tmp_buf (EVP_MAX_MD_SIZE);
         unsigned int size = 0;
         if (1 == EVP_DigestFinal_ex(&mdctx, tmp_buf, &size))
         {
            rv.assign (tmp_buf, size);
            succeeded = true;
         }
         
         EVP_MD_CTX_cleanup(&mdctx);
      }
      
      if (!succeeded)
         throw SSL_ERROR;
      
      return rv;
   }
   
   ustring
      make_xml_encoded_signature (const ustring &xml_signing_private_key,
      const ustring &message)
   {
      ustring rv;
      
      const ustring digest = make_digest (message);
      
      auto_DSA keypair (DSA_from_xml (xml_signing_private_key,
         false));

      auto_DSA_SIG sig (DSA_do_sign (digest.data (),
                                     digest.size (),
                                     keypair));
         
      if (sig)
      {
         unsigned char *der_encoded_sig = NULL;
         int length = i2d_DSA_SIG(sig, &der_encoded_sig);
         if (length >= 0)
         {
            const ustring tmp =
               b64_encode ((const char *)der_encoded_sig, length);
            OPENSSL_free (der_encoded_sig);
               
            rv = xml_wrap (SIGNATURE, tmp);
         }
      }

      if (!rv.length ())
         throw SSL_ERROR;
      
      return rv;
   }
   
   /* This function does a bunch of things at once.
   
     1) It checks that the content is well-formed XML, and throws an
     XML_ERROR if not.
     
       2) It then checks that the root element's name is
       expected_root_tag, and throws an XML_ERROR if not.  This amounts
       to very simple validation.
       
         3) Once it gets that far, it returns the characters from the root
         element. 
   */
   ustring
      xml_1st_elt_content (const char *const expected_root_tag,
      const ustring &content)
   {
      ustring rv;
      VHUtil::xml_tree xt ((const char *) content.c_str ());
      if (xt.root ()->name () != expected_root_tag)
      {
         std::ostringstream whine;
         whine << "Expected `"
            << expected_root_tag
            << "' element, but got `"
            << xt.root ()->name ()
            << "'";
         throw XML_ERROR (whine.str ().c_str ());
      }
      
      return (const unsigned char *) (xt.root ()->characters ()).c_str ();
   }
   
   inline
      ustring
      xml_1st_elt_content (const char *const expected_root_tag,
      const std::string &content)
   {
      return xml_1st_elt_content (expected_root_tag,
         (const unsigned char *)content.c_str ());
   }
   
   bool
      is_valid_sig (const ustring &xml_signing_public_key,
      const ustring &message,
      const ustring &xml_sig)
   {
      bool rv = false;
      
      const ustring der_sig = b64_decode (xml_1st_elt_content (SIGNATURE,
         xml_sig));
      const ustring digest  = make_digest (message);
      
      auto_DSA dsa_params (DSA_from_xml (xml_signing_public_key,
         true));

      int status = DSA_verify (0,                /* type -- ignored */
                               digest.data (),
                               digest.size (),
                               der_sig.data (),
                               der_sig.size (),
                               dsa_params);

      const int lib    = ERR_GET_LIB    (ERR_get_error ());
      const int func   = ERR_GET_FUNC   (ERR_get_error ());
      const int reason = ERR_GET_REASON (ERR_get_error ());
      
      switch (status)
      {
      case 0:
         rv = false;
         break;
      case 1:
         rv = true;
         break;
      default:
      {
         std::ostringstream whine;
         whine << "OpenSSL error "
               << VHUtil::ssl_errors ()
               << " checking signature";
         throw VH_exception (whine.str ().c_str ());
      }
      }

      return rv;
   }
}

int
VHTI_sign_xml (GeneralPurposePrivateKey prv,
               ConstCharStar xml_plaintext,
               ConstCharStar *signed_xml)
{
   int result = 0;
   
   try {
      if (::VHTI_validate (GENERAL_PURPOSE_PRIVATE_KEY, prv))
         throw XML_ERROR (prv);

      VHUtil::xml_tree tbs (xml_plaintext);
      *signed_xml = 0;

      VHUtil::xml_tree blob_tree ("<"
                                  + VHInternal::signed_xml_root_element_prefix
                                  + tbs.root ()->name ()
                                  + "/>");

      const char *signature = 0;

      if (VHTI_sign (prv,
                     xml_plaintext,
                     &signature))
         throw VH_exception ("CANNOT_SIGN");

      blob_tree.root ()->new_element (SIGNED_DATA)->add_characters (xml_plaintext);
      blob_tree.root ()->new_element (SIGNATURE)->add_characters
         (VHUtil::xml_tree (signature).root ()->characters ());

      VHTI_free (signature);
      *signed_xml = VHTI_dup (blob_tree.str ().c_str ());
   }
   catch (const VHUtil::Exception & e)
   {
      VHTI_set_last_error(e);
      VHUtil::cout() << e.what () << std::endl;
      result = e.getResultNo();
   }
   
   return result;
}

int
VHTI_sign(GeneralPurposePrivateKey private_key,
          ConstCharStar plaintext,
          Signature *signature)
{
   int result = 0;
   
   try
   {
      if (::VHTI_validate (GENERAL_PURPOSE_PRIVATE_KEY, private_key))
         throw XML_ERROR (private_key);
      
      ustring sig = make_xml_encoded_signature ((unsigned char *) private_key,
         (unsigned char *) plaintext);
      *signature = VHTI_dup ((char *) sig.c_str ());
   }
   catch (const VHUtil::Exception & e)
   {
      VHTI_set_last_error(e);
      VHUtil::cout() << e.what () << std::endl;
      result = e.getResultNo();
   }
   
   return result;
}

int
VHTI_verify_signature(GeneralPurposePublicKey public_key,
                      ConstCharStar plaintext,
                      Signature signature,
                      CheckResults *c_result)
{
   int result = 0;
   
   *c_result = 0;
   
   if (0 == strcmp ("NO_SIGNATURE_CHECK", public_key))
      *c_result = VHTI_dup (CHECK_SUCCESS_XML);
   else
   {
      try
      {
         if (::VHTI_validate (GENERAL_PURPOSE_PUBLIC_KEY, public_key))
            throw XML_ERROR (public_key);
         if (::VHTI_validate (SIGNATURE, signature))
            throw XML_ERROR (signature);
      
         *c_result = VHTI_dup (is_valid_sig ((unsigned char *) public_key,
                                             (unsigned char *)plaintext,
                                             (unsigned char *)signature)
                               ? CHECK_SUCCESS_XML
                               : CHECK_FAILURE_XML);
      }
      catch (const VHUtil::Exception & e)
      {
         VHTI_set_last_error(e);
         VHUtil::cout() << e.what () << std::endl;
         result = e.getResultNo();
      }
   }
   return result;
}

int
VHTI_check_xml (GeneralPurposePublicKey public_key,
                ConstCharStar signed_xml,
                ConstCharStar expected_root_element_name,
                CheckResults *c_result,
                ConstCharStar *inner_xml)
{
   int result = 0;
   
   *c_result = 0;
   *inner_xml = 0;

   try
   {
      VHUtil::safe_xml_tree tbs (signed_xml, expected_root_element_name, public_key);
      std::ostringstream tmp;
      tmp << tbs;
      *inner_xml = VHTI_dup (tmp.str ().c_str ());
      *c_result = VHTI_dup (CHECK_SUCCESS_XML);
   }
   catch (const VHUtil::Exception & e)
   {
      if (e.getResultId ().find (CHECK_FAILURE_XML) != e.getResultId ().npos)
      {
         *c_result = VHTI_dup (CHECK_FAILURE_XML);
         *inner_xml = VHTI_dup ("The signature didn't check, so there's no point extracting the inner XML.");
      }
      else
      {
         VHTI_set_last_error(e);
         VHUtil::cout() << e.what () << std::endl;
         result = e.getResultNo();
      }
   }

   return result;
}
