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

// Encryption uses the AES cipher in cipher block chaining mode.  We
// chose AES over other algorithms simply because Schneier and
// Ferguson recommend it in "Practical Cryptography" (Wiley, 2003); we
// chose CBC mode because it is one of "only two modes [they] would
// consider using".  The other mode was CTR, which they prefer, but as
// of June 2003, the current version of OpenSSL (namely 0.9.7b)
// doesn't implement that mode with AES.

#include "vhti/crypt.h"
#include <support/internal_error.h>
#include <support/bignum.h>
#include <misc/array.h>
#include <misc/vh_excpt.h>
#include <misc/format_string.h>
#include <misc/vh_cout.h>
#include <misc/xml_tree.h>
#include <openssl/rsa.h>
#include <openssl/err.h>
#include <openssl/pem.h>

#include <string>
#include <sstream>

#include "misc.h"

namespace {
      
   class free_RSA {
   public:
      static void free(RSA *x)
      {
         RSA_free(x);
      }
   };
   
   typedef auto_C_PTR<RSA, free_RSA> auto_RSA;
   
   class free_EVP_PKEY {
   public:
      static void free (EVP_PKEY *x)
      {
         EVP_PKEY_free (x);
      }
   };
   
   typedef auto_C_PTR<EVP_PKEY, free_EVP_PKEY> auto_EVP_PKEY;
   
   
   // call RSA_free on the returned result, if it isn't NULL
   RSA *
      RSA_from_xml (const char *xml,
      const bool public_only)
   {
      RSA *rv = 0;
      
      VHUtil::xml_tree xt (xml);
      std::string pem_encoded = xt.root ()->e (public_only
         ? ENCRYPTION_PUBLIC_KEY
         : ENCRYPTION_PRIVATE_KEY)->characters ();
      
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
         rv = PEM_read_bio_RSA_PUBKEY (mem,
            NULL,
            NULL,
            NULL);
      }
      else
      {
         rv = PEM_read_bio_RSAPrivateKey (mem,
            NULL,
            NULL,
            NULL);
      }
      
      return rv;
   }
   
   std::ostream &
      hexdump (std::ostream &o,
      const ustring &us)
   {
      o << std::hex;
      for (size_t chars_output = 0;
      chars_output < us.size ();
      chars_output++)
      {
         const unsigned short int x = us[chars_output];
         const unsigned short lower = x % 16;
         const unsigned short upper = x >> 4;
         o << " "
            << upper
            << lower;
      }
      o << std::dec;
      return o;
   }

   std::string
      b64_encode (const ustring &binary_stuff)
   {
      ustring tmp (::b64_encode ((const char *) (binary_stuff.data ()),
         binary_stuff.size ()));
      return ((const char *) tmp.c_str ());
   }
   
   ustring
      b64_decode (const std::string &message)
   {
      return (::b64_decode ((const unsigned char *) (message.data ())));
   }
   
   
   // plaintext is any arbitrary data.  outputs are binary.  The return
   // value, also binary, is the ciphertext bytes.
   
   // The function indicates failure by returning an empty string.
   ustring
      rsa_aes_encrypt (RSA *rsa,
      const ustring &plaintext,
      ustring &session_key,
      ustring &initialization_vector)
   {
      ustring ciphertext_bytes;
      EVP_CIPHER_CTX ectx;
      unsigned char iv[EVP_MAX_IV_LENGTH];
      int ekeylen = 0; 
      
      memset (&ectx, '\0', sizeof (ectx));
      memset (iv, '\0', sizeof (iv));
      
      EVP_PKEY *pubKey[1];
      auto_EVP_PKEY pubKeyOne (EVP_PKEY_new ());
      VH_nonzero (pubKeyOne, EVP_PKEY_NEW);
      pubKey [0] =  pubKeyOne;
      
      if (!pubKey[0])
         throw SSL_ERROR;
      
      if (1 != EVP_PKEY_set1_RSA (pubKey[0],
         rsa))
         throw SSL_ERROR;
      
      unsigned char* ekey[1];
      VHUtil::array<unsigned char> ekey_one (EVP_PKEY_size (pubKey[0]));
      ekey[0] = ekey_one; 
      memset (ekey[0], '\0', EVP_PKEY_size (pubKey[0]));
      
      if (!EVP_SealInit (&ectx,
         EVP_aes_256_cbc (),
         ekey,
         &ekeylen,
         iv,
         pubKey,
         1))
         throw SSL_ERROR;
      
      initialization_vector.assign (iv, sizeof (iv));
      session_key.assign (ekey[0], EVP_PKEY_size (pubKey[0]));
      
      {
         int ebuflen = 0;
         VHUtil::array<unsigned char> ebuf(plaintext.size()+ EVP_MAX_IV_LENGTH);
         if (!EVP_SealUpdate (&ectx,
            ebuf,
            &ebuflen,
            plaintext.data (),
            plaintext.size ()))
            throw SSL_ERROR;
         
         {
            int tmplen = 0;
            if (!EVP_SealFinal (&ectx,
               ebuf + ebuflen,
               &tmplen))
               throw SSL_ERROR;
            
            ebuflen += tmplen;
         } 
         
         ciphertext_bytes.assign (ebuf, ebuflen);
      }
      
      return ciphertext_bytes;
   }
   
   ustring
      rsa_aes_decrypt (RSA *rsa,
      const ustring &session_key,
      const ustring &initialization_vector,
      const ustring &ciphertext)
   {
      ustring rv;
      EVP_CIPHER_CTX ectx;
      unsigned char iv[EVP_MAX_IV_LENGTH];
      
      memset (&ectx, '\0', sizeof (ectx));
      
      if (sizeof (iv) != initialization_vector.size ())
      {
         std::ostringstream whine;
         whine << "Initialization Vector was "
            << initialization_vector.size ()
            << " bytes, but ought to have been "
            << EVP_MAX_IV_LENGTH
            << " bytes";
         throw VHUtil::Exception (__FILE__, __LINE__, whine.str ().c_str ());
      }
      
      memcpy (iv,
         initialization_vector.data (),
         initialization_vector.size ());
      
      auto_EVP_PKEY prvKey (EVP_PKEY_new ());
      
      if(!prvKey)
         throw SSL_ERROR;
      
      if (1 != EVP_PKEY_set1_RSA(prvKey,
         rsa))
         throw SSL_ERROR;
      
      if (EVP_PKEY_size(prvKey) != session_key.size ())
      {
         std::ostringstream whine;
         whine << "Session Key was "
            << session_key.size ()
            << " bytes, but ought to have been "
            << EVP_PKEY_size (prvKey)
            << " bytes";
         throw VHUtil::Exception (__FILE__, __LINE__, whine.str ().c_str ());
      }
      
      VHUtil::array<unsigned char> ekey (EVP_PKEY_size(prvKey)); 
      memcpy (ekey, session_key.data (),
         session_key.size ());
      
      {
         if (!EVP_OpenInit (&ectx,
            EVP_aes_256_cbc(),
            ekey,
            EVP_PKEY_size (prvKey),
            iv,
            prvKey))
            throw SSL_ERROR;
         
         {
            VHUtil::array<unsigned char> plaintext(ciphertext.size() +
               EVP_CIPHER_CTX_block_size (&ectx));
            memset (plaintext, '\xee', ciphertext.size () +
               EVP_CIPHER_CTX_block_size (&ectx));
            int plaintext_length = 0;
            
            if (!EVP_OpenUpdate (&ectx,
               plaintext,
               &plaintext_length,
               ciphertext.data (),
               ciphertext.size ()))
               throw SSL_ERROR;
            
            {
               int tmplen = 0;
               if (!EVP_OpenFinal(&ectx,
                  plaintext + plaintext_length,
                  &tmplen))
                  throw SSL_ERROR;
               plaintext_length += tmplen;
            } 
            
            rv.assign (plaintext,
               plaintext_length);
         }
      }
      
      return rv;
   }
   
}

int
VHTI_encrypt(GeneralPurposePublicKey public_key,
             ConstCharStar plaintext,
             EncryptedData *encrypted_data)
{
   int result = 0;
   *encrypted_data = 0;
   
   try
   {
      if (::VHTI_validate (GENERAL_PURPOSE_PUBLIC_KEY, public_key))
         throw XML_ERROR (public_key);
      
      auto_RSA rsa (RSA_from_xml (public_key,
         true));
      
      if (!rsa)
         throw SSL_ERROR;
      
      VHUtil::array<unsigned char> tmp ((RSA_size (rsa)) + 1);
      
      std::string ciphertext_b64;
      std::string session_key_b64;
      std::string initialization_vector_b64;
      {
         ustring binary_session_key;
         ustring binary_initialization_vector;
         const ustring binary_ciphertext = rsa_aes_encrypt (rsa,
            (const unsigned char *) plaintext,
            binary_session_key,
            binary_initialization_vector);
         if (!binary_ciphertext.size ())
            throw SSL_ERROR;
         
         ciphertext_b64            = b64_encode (binary_ciphertext);
         session_key_b64           = b64_encode (binary_session_key);
         initialization_vector_b64 = b64_encode (binary_initialization_vector);
      }
      
      VHUtil::xml_tree xt ("<" ENCRYPTED_DATA "/>");
      xt.root()->new_element (INITIALIZATION_VECTOR)->
         add_characters (initialization_vector_b64);
      xt.root()->new_element (ENCRYPTED_SESSION_KEY)->
         add_characters (session_key_b64);
      xt.root()->new_element (CIPHER_TEXT          )->
         add_characters (ciphertext_b64);
      
      {
         std::ostringstream tmp;
         tmp << *(xt.root ());
         
         *encrypted_data = VHTI_dup (tmp.str ().c_str ());
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

int
VHTI_decrypt(GeneralPurposePrivateKey private_key,
             EncryptedData xml_b64_encrypted_data,
             ConstCharStar *plaintext)
{
   int result = 0;
   *plaintext = 0;
   
   try
   {
      if (::VHTI_validate (GENERAL_PURPOSE_PRIVATE_KEY, private_key))
         throw XML_ERROR (private_key);
      if (::VHTI_validate (ENCRYPTED_DATA, xml_b64_encrypted_data))
         throw XML_ERROR (xml_b64_encrypted_data);
      
      auto_RSA rsa (RSA_from_xml (private_key,
         false));
      if (!rsa)
         throw SSL_ERROR;
      
      VHUtil::xml_tree xt (xml_b64_encrypted_data);
      const ustring binary_initialization_vector (b64_decode (xt.root ()->e
         (INITIALIZATION_VECTOR)->characters ()));
      const ustring binary_session_key           (b64_decode (xt.root ()->e
         (ENCRYPTED_SESSION_KEY)->characters ()));
      const ustring binary_ciphertext            (b64_decode (xt.root ()->e
         (CIPHER_TEXT          )->characters ()));
      
      ustring plain = rsa_aes_decrypt (rsa,
         binary_session_key,
         binary_initialization_vector,
         binary_ciphertext);
      
      *plaintext = VHTI_dup ((const char *)plain.c_str ());
      
      if (!*plaintext)
         throw SSL_ERROR;
   }
   catch (const VHUtil::Exception & e)
   {
      VHTI_set_last_error(e);
      VHUtil::cout() << e.what () << std::endl;
      result = e.getResultNo();
   }
   return result;
}

namespace {
ustring
password_aes_encrypt (const ustring &plaintext,
                      const unsigned char *password)
{
   ustring ciphertext_bytes;
   EVP_CIPHER_CTX ectx;
   unsigned char iv[EVP_MAX_IV_LENGTH];
   int ekeylen = 0; 
   
   memset (&ectx, '\0', sizeof (ectx));
   memset (iv, '\0', sizeof (iv));
   
   if (!EVP_EncryptInit (&ectx,
      EVP_aes_256_cbc (),
      password,
      iv))
      throw SSL_ERROR;
   
   {
      int ebuflen = 0;
      VHUtil::array<unsigned char> ebuf(plaintext.size()+ EVP_MAX_IV_LENGTH);
      if (!EVP_EncryptUpdate (&ectx,
         ebuf,
         &ebuflen,
         plaintext.data (),
         plaintext.size ()))
         throw SSL_ERROR;
      
      {
         int tmplen = 0;
         if (!EVP_EncryptFinal (&ectx,
            ebuf + ebuflen,
            &tmplen))
            throw SSL_ERROR;
         
         ebuflen += tmplen;
      } 
      
      ciphertext_bytes.assign (ebuf, ebuflen);
   }
   
   return ciphertext_bytes;
}

ustring
password_aes_decrypt (const unsigned char *password,
                      const ustring &ciphertext)
{
   ustring rv;
   EVP_CIPHER_CTX ectx;
   unsigned char iv[EVP_MAX_IV_LENGTH];
   
   memset (&ectx, '\0', sizeof (ectx));
   memset (iv, '\0', sizeof (iv));
   
   {
      if (!EVP_DecryptInit (&ectx,
         EVP_aes_256_cbc(),
         password,
         iv))
         throw SSL_ERROR;
      
      {
         VHUtil::array<unsigned char> plaintext(ciphertext.size() +
            EVP_CIPHER_CTX_block_size (&ectx));
         memset (plaintext, '\xee', ciphertext.size () +
            EVP_CIPHER_CTX_block_size (&ectx));
         int plaintext_length = 0;
         
         if (!EVP_DecryptUpdate (&ectx,
            plaintext,
            &plaintext_length,
            ciphertext.data (),
            ciphertext.size ()))
            throw SSL_ERROR;
         
         {
            int tmplen = 0;
            if (!EVP_DecryptFinal(&ectx,
               plaintext + plaintext_length,
               &tmplen))
               throw SSL_ERROR;
            plaintext_length += tmplen;
         } 
         
         rv.assign (plaintext,
            plaintext_length);
      }
   }
   
   return rv;
}
}

int
VHTI_password_encrypt(Password password,
                      ConstCharStar plaintext,
                      PasswordEncryptedData *encrypted_data)
{
   int result = 0;
   *encrypted_data = 0;
   
   try
   {
      if (::VHTI_validate (PASSWORD, password))
         throw XML_ERROR (password);

      VHUtil::xml_tree xml_pw(password);
      std::string str_pw = xml_pw.root()->characters();
      // Get a hash of the password
      auto_BN pw_bn = BN_bin2bn((unsigned char *) str_pw.c_str(), str_pw.size(), 0);
      if (!pw_bn)
         throw SSL_ERROR;

      const BIGNUM *arr[] = {pw_bn};
      auto_BN pw_hash = GetHashOfNBNs(arr, sizeof(arr) / sizeof(arr[0]));
      char * pw_decimal_hash = BN_bn2dec(pw_hash);
      if (0 == static_cast<const char *>(pw_decimal_hash))
         throw SSL_ERROR;
      
      std::string ciphertext_b64;
      {
         const ustring binary_ciphertext = password_aes_encrypt ( (const unsigned char *) plaintext,
            (const unsigned char *) pw_decimal_hash);
         
         if (!binary_ciphertext.size ())
            throw SSL_ERROR;
         
         ciphertext_b64            = b64_encode (binary_ciphertext);
      }

      VHUtil::xml_tree xt ("<" PASSWORD_ENCRYPTED_DATA "/>");
      xt.root()->new_element (CIPHER_TEXT          )->
         add_characters (ciphertext_b64);
      
      {
         std::ostringstream tmp;
         tmp << *(xt.root ());
         
         *encrypted_data = VHTI_dup (tmp.str ().c_str ());
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

int
VHTI_password_decrypt(Password password,
                      PasswordEncryptedData xml_b64_encrypted_data,
                      ConstCharStar *plaintext)
{
   int result = 0;
   *plaintext = 0;
   
   try
   {
      if (::VHTI_validate (PASSWORD, password))
         throw XML_ERROR (password);
      if (::VHTI_validate (PASSWORD_ENCRYPTED_DATA, xml_b64_encrypted_data))
         throw XML_ERROR (xml_b64_encrypted_data);

      VHUtil::xml_tree xml_pw(password);
      std::string str_pw = xml_pw.root()->characters();
      // Get a hash of the password
      auto_BN pw_bn = BN_bin2bn((unsigned char *) str_pw.c_str(), str_pw.size(), 0);
      if (!pw_bn)
         throw SSL_ERROR;

      const BIGNUM *arr[] = {pw_bn};
      auto_BN pw_hash = GetHashOfNBNs(arr, sizeof(arr) / sizeof(arr[0]));
      char * pw_decimal_hash = BN_bn2dec(pw_hash);
      if (0 == static_cast<const char *>(pw_decimal_hash))
         throw SSL_ERROR;

      VHUtil::xml_tree xt (xml_b64_encrypted_data);
      const ustring binary_ciphertext            (b64_decode (xt.root ()->e
         (CIPHER_TEXT          )->characters ()));
      
      ustring plain = password_aes_decrypt ((const unsigned char *) pw_decimal_hash,
         binary_ciphertext);
      
      *plaintext = VHTI_dup ((const char *)plain.c_str ());
      
      if (!*plaintext)
         throw SSL_ERROR;
   }
   catch (const VHUtil::Exception & e)
   {
      VHTI_set_last_error(e);
      VHUtil::cout() << e.what () << std::endl;
      result = e.getResultNo();
   }
   return result;
}
