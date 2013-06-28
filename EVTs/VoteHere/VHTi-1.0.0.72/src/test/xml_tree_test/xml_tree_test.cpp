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
# pragma warning (disable: 4305 4309 4786)
#endif

#include <vhti/types.h>
#include <misc/file_contents.h>
#include <misc/xml_tree.h>
#include <misc/safe_xml_tree.h>
#include <misc/vh_excpt.h>
#include <vhti/support.h>
#include <vhti/sign.h>
#include <vhti/genkeys.h>
#include <util/validate.h>
#include <iostream>
#include <sstream>
#include <memory>
#include <iomanip>

extern "C" {
#include <misc/CuTest.h>
}

CuSuite *my_suite = NULL;

namespace {

// "I can eat glass; it doesn't hurt me" in Hebrew ;-)
   const char hebrew_utf8 [] = {
      0xd7, 0x90, 0xd7, 0xa0, 0xd7, 0x99, 0x20, 0xd7, 0x99, 0xd7, 0x9b, 0xd7, 0x95, 0xd7,
      0x9c, 0x20, 0xd7, 0x9c, 0xd7, 0x90, 0xd7, 0x9b, 0xd7, 0x95, 0xd7, 0x9c, 0x20, 0xd7,
      0x96, 0xd7, 0x9b, 0xd7, 0x95, 0xd7, 0x9b, 0xd7, 0x99, 0xd7, 0xaa, 0x20, 0xd7, 0x95,
      0xd7, 0x96, 0xd7, 0x94, 0x20, 0xd7, 0x9c, 0xd7, 0x90, 0x20, 0xd7, 0x9e, 0xd7, 0x96,
      0xd7, 0x99, 0xd7, 0xa7, 0x20, 0xd7, 0x9c, 0xd7, 0x99, 0x2e, 0x00
   };
   const char hebrew_as_entities[] = "&#x5d0;&#x5e0;&#x5d9; &#x5d9;&#x5db;&#x5d5;&#x5dc; &#x5dc;&#x5d0;&#x5db;&#x5d5;&#x5dc; &#x5d6;&#x5db;&#x5d5;&#x5db;&#x5d9;&#x5ea; &#x5d5;&#x5d6;&#x5d4; &#x5dc;&#x5d0; &#x5de;&#x5d6;&#x5d9;&#x5e7; &#x5dc;&#x5d9;.";

// "I can eat glass; it doesn't hurt me" in Spanish
   const char valid_spanish_latin_1 [] = {

      0x50, 0x75, 0x65, 0x64, 0x6f, 0x20, 0x63, 0x6f, 0x6d, 0x65,
      0x72, 0x20, 0x76, 0x69, 0x64, 0x72, 0x69, 0x6f, 0x2c, 0x20,
      0x6e, 0x6f, 0x20, 0x6d, 0x65, 0x20, 0x68, 0x61, 0x63, 0x65,
      0x20, 0x64, 0x61, 0xf1, 0x6f, 0x2e, 0x00
   };

// The same, but UTF-8.
   const char valid_spanish_utf8 [] = {

      0x50, 0x75, 0x65, 0x64, 0x6f, 0x20, 0x63, 0x6f, 0x6d, 0x65,
      0x72, 0x20, 0x76, 0x69, 0x64, 0x72, 0x69, 0x6f, 0x2c, 0x20,
      0x6e, 0x6f, 0x20, 0x6d, 0x65, 0x20, 0x68, 0x61, 0x63, 0x65,
      0x20, 0x64, 0x61, 0xc3, 0xb1, 0x6f, 0x2e, 0x00
   };

// The same, but encoded as XML entities.
   const char valid_spanish_entities [] = "Puedo comer vidrio, no me hace da&#xF1;o.";

   void
   expect_exception (CuTest *tc,
                     const std::string &data)
   {
      std::auto_ptr<VHUtil::xml_tree> pTree;
      bool f_proper_exception_caught = false;
      try
      {
         // I'd rather simply call pTree.reset, but that method
         // doesn't exist in Microsoft VC++ 6.0's broken STL
         std::auto_ptr<VHUtil::xml_tree> tmp (new VHUtil::xml_tree (data));
         pTree = tmp;
         std::ostringstream bit_bucket;
         bit_bucket << *pTree;
      }
      catch (VHUtil::Exception)
      {
         f_proper_exception_caught = true;
      }
      catch (...)
      {
         std::clog << "Have you ensured that VHUtil::Result has access to its XML file full of error messages?";
      }

      CuAssert (tc,
                "didn't catch the exception we expected",
                f_proper_exception_caught);
   }

   void not_XML (CuTest *tc)
   {
      expect_exception (tc, "");
      expect_exception (tc, "This isn't XML at all.");
      expect_exception (tc, "<?xml version=\"1.0\" encoding=\"ISO-8859-1-goofball\"?>\n");
   }

   void accepts_UTF_8 (CuTest *tc)
   {
      const std::string headline = "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n";
      std::string xml_with_utf_8_pcdata = headline;

      std::string expected_utf8;
      expected_utf8 += "<bob>";
      expected_utf8 += hebrew_utf8;
      expected_utf8 += "</bob>";

      xml_with_utf_8_pcdata += expected_utf8;
      
      // Stuff in some UTF-8 characters, see if we can get them back
      // out.
      {
         VHUtil::xml_tree Tree (xml_with_utf_8_pcdata);
         VHUtil::xml_tree::node *root = Tree.root();

         std::string returned_chars = root->characters ();
         CuAssert (tc,
                   "method `characters' returned wrong characters",
                   returned_chars == hebrew_utf8);
         {
            std::ostringstream tmp;
            std::ostringstream whine;
            std::string expected_entities;
            expected_entities += "<bob>";
            expected_entities += hebrew_as_entities;
            expected_entities += "</bob>";

            try {
               tmp << *root;
               whine << "expected "
                     << std::endl
                     << expected_entities
                     << std::endl
                     << "; got "
                     << std::endl
                     << tmp.str ()
                     << std::endl;
            } catch (...) {
               whine << "Got an exception";
            }

            CuAssert (tc,
                      const_cast<char *>(whine.str ().c_str ()),
                      0 == stricmp (expected_entities.c_str (), tmp.str ().c_str ()));
         }
      }

      // Now stuff in an attribute value that is UTF-8, and see if we
      // can get *that* back out.

      std::string xml_with_attributes_utf_8 = headline;
      xml_with_attributes_utf_8 += "<bob foo=\"";
      xml_with_attributes_utf_8 += hebrew_utf8;
      xml_with_attributes_utf_8 += "\">hey you</bob>\n";

      VHUtil::xml_tree Tree (xml_with_attributes_utf_8);
      VHUtil::xml_tree::node *root = Tree.root();
      std::string returned_chars = root->attribute ("foo");

      CuAssert (tc,
                "wrong characters returned",
                returned_chars == hebrew_utf8);
   }

   void accepts_Latin_1 (CuTest *tc)
   {
      // Ditto for Latin-1 ...

      std::string latin_1_xml = "<?xml version=\"1.0\" encoding=\"ISO-8859-1\"?>\n";

      latin_1_xml += "<bob>";
      latin_1_xml += valid_spanish_latin_1;
      latin_1_xml += "</bob>\n";

      // Stuff in the Latin-1 characters, see if we can get them
      // back out as UTF-8.
      {
         VHUtil::xml_tree Tree (latin_1_xml);
         VHUtil::xml_tree::node *root = Tree.root();

         std::string returned_utf8 = root->characters ();
         std::string returned_entities;
         {
            std::ostringstream tmp;
            tmp << *root;
            returned_entities = tmp.str ();
         }

         std::string expected_entities;
         expected_entities += "<bob>";
         expected_entities += valid_spanish_entities;
         expected_entities += "</bob>";

         CuAssert (tc,
                   "Wrong characters returned",
                   returned_utf8 == valid_spanish_utf8);

         CuAssert (tc,
                   "Wrong characters returned",
                   0 == stricmp (returned_entities.c_str (), expected_entities.c_str ()));
      }
   }

   std::string hex_codes (const std::string &input)
   {
      std::ostringstream tmp;
      tmp << std::hex;
      for (unsigned int chars_processed = 0;
           chars_processed < input.size ();
           chars_processed++)
      {
         if (chars_processed)
            tmp << " ";
         tmp << "0x"
             << std::setfill ('0')
             << std::setw(2)
             << (unsigned int) input[chars_processed];
      }
      return tmp.str ();
   }
   
   void one_canon_test (CuTest *tc,
                        const std::string &before,
                        const std::string &expected_after)
   {
      VHUtil::xml_tree Tree (before);
      std::string actual_after;
      {
         std::ostringstream tmp;
         tmp << *(Tree.root ());
         actual_after = tmp.str ();
      }
      std::ostringstream whine;

      whine << std::endl
            << "Before         : `" << before << "'"
            << std::endl
            << "Expected after : `" << expected_after  << "'"
            << std::endl
            << "Actual   after : `" << actual_after    << "'"
            << std::endl
            << "Expected: " << hex_codes (expected_after)
            << std::endl
            << "Actual  : " << hex_codes (actual_after);

      CuAssert (tc,
                (char *) (whine.str ().c_str ()),
                expected_after == actual_after);
   }
   
   void all_canon_tests (CuTest *tc)
   {
      // random musings on how I *think* this should work.  It's all
      // depressingly dependent on the behavior of libxml2, which is
      // probably neither standardized nor guaranteed.

      // When libxml reads input, it translates \r\n to \n, and \r not
      // followed by \n to \n.  http://www.w3.org/TR/REC-xml, section
      // 2.11, says to do that.
      
      // When it emits output via xmlEncodeEntitiesReentrant, it
      // translates \r to &#13;.  This (along with the above) implies
      // that we'll see &x13; in the output only when it also appeared
      // in the input.

      one_canon_test (tc,
                      "<a>\r</a>",
                      "<a>\n</a>");

      one_canon_test (tc,
                      "<a>&#13;</a>",
                      "<a>&#13;</a>");

      one_canon_test (tc,
                      "<a>&#xd;&#10;</a>",
                      "<a>&#13;\n</a>");

      one_canon_test (tc,
                      "<a>&#13;&#10;</a>",
                      "<a>&#13;\n</a>");

      one_canon_test (tc,
                      "<a>\r\n</a>",
                      "<a>\n</a>");

      one_canon_test (tc,
                      "<a>\r&#x1234;\n</a>",
                      "<a>\n&#x1234;\n</a>");

      one_canon_test (tc,
                      "<a>\r&#12345;\n</a>",
                      "<a>\n&#x3039;\n</a>");
   }
   
   void notices_invalid_UTF_8 (CuTest *tc)
   {
      std::string utf_8_xml = "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n";
      utf_8_xml += "<tiny>\ncan text go here?\nHere's a non-UTF byte sequence:\212\n</tiny>";
      const std::string dtd = "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n<!ELEMENT tiny ANY >\n";

      CuAssert (tc,
                "failed to notice invalid UTF-8",
                false == VHUtil::validate_xml_document(utf_8_xml,
                                                       dtd,
                                                       false));
   }

   void validates_valid_UTF_8 (CuTest *tc)
   {
      std::string utf_8_xml = "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n";
      utf_8_xml += "<tiny>\n";
      utf_8_xml += hebrew_utf8;
      utf_8_xml += "\n</tiny>";
      const std::string dtd = "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n<!ELEMENT tiny ANY >\n";

      CuAssert (tc,
                "failed to validate valid UTF-8",
                true == VHUtil::validate_xml_document(utf_8_xml,
                                                      dtd,
                                                      false));
   }

   void deep_copy_works(CuTest *tc)
   {
      std::string data_part("<data name=\"foo\">this<space> </space>is<space> </space>some<space> </space>data</data>");
      VHUtil::xml_tree source("<source>" + data_part + "</source>");
      VHUtil::xml_tree dest("<dest></dest>");
      VHUtil::xml_node n = source.root()->e("data");
      dest.root()->add_element(n->deep_copy());
      std::ostringstream s;
      s << dest;
      CuAssert (tc,
                "didn't properly deep-copy",
                ("<dest>" + data_part + "</dest>")
                == s.str());
   }

   const std::string expected_serialized = "<" BIG_GAMMA " Encoding=\"DEC\"" "></" BIG_GAMMA ">";

   std::string good_pub_key;
   std::string good_private_key;

   std::string signature;
   
   void safe_xml_tree (CuTest *tc)
   {
      auto_freeing<ConstCharStar> signed_blob = 0;
      CuAssert (tc,
                "VHTI_sign_xml unexpectedly failed",
                !VHTI_sign_xml (good_private_key.c_str (),
                                expected_serialized.c_str (),
                                &signed_blob));

      VHUtil::safe_xml_tree safe_tree (static_cast<const char *> (signed_blob),
                                       BIG_GAMMA,
                                       good_pub_key);

      // Ensure that it serializes properly.
      {
         bool fThrew = false;
         try {
            const std::string actual_serialzed (safe_tree);
            std::ostringstream whine;
            whine << "Expected `"
                  << expected_serialized
                  << "'; instead got `"
                  << actual_serialzed
                  << "'";
            CuAssert (tc,
                      (char *) (whine.str ().c_str ()),
                      actual_serialzed == expected_serialized);
         }
         catch (...)
         {
            fThrew = true;
         }

         CuAssert (tc,
                   "improperly threw an exception",
                   !fThrew);
      }

      // Test that the ctor actually checks the signature.

      bool f_threw_correct_exception = false;
      {
         VHUtil::xml_tree blob_tree (static_cast<const char *> (signed_blob));

         VHUtil::xml_tree tree_with_corrupt_sig ("<"
                                          + blob_tree.root ()->name ()
                                          + "/>");
         tree_with_corrupt_sig.root ()->new_element (SIGNED_DATA)->add_characters (expected_serialized);
         tree_with_corrupt_sig.root ()->new_element (SIGNATURE  )->add_characters ("Not a base64-encoded signature at all");
         try {
            VHUtil::safe_xml_tree should_not_exist (tree_with_corrupt_sig,
                                                    BIG_GAMMA,
                                                    good_pub_key);
         } catch (VHUtil::Exception &) {
            f_threw_correct_exception = true;
         }
         CuAssert (tc,
                   "Failed to notice bad signature",
                   f_threw_correct_exception);
      }

      // Just for laughs, check that it notices a bad public key, too.
      f_threw_correct_exception = false;
      try {
         VHUtil::safe_xml_tree should_not_exist (static_cast<const char *> (signed_blob),
                                                 BIG_GAMMA,
                                                 "this doesn't even remotely resemble a public key.");
      } catch (...) {
         f_threw_correct_exception = true;
      }
      CuAssert (tc,
                "Failed to notice bad public key",
                f_threw_correct_exception);

      f_threw_correct_exception = false;
      try {
         VHUtil::safe_xml_tree should_not_exist (static_cast<const char *> (signed_blob),
                                                 BIG_GAMMA,
                                                 "<GeneralPurposePublicKey><IdentInfo></IdentInfo><SigningPublicKey>"
                                                 "-----BEGIN PUBLIC KEY-----\n"
                                                 "this is public key is valid according to the DTD, but is utterly bogus"
                                                 "from OpenSSL's point of view."
                                                 "-----END PUBLIC KEY-----\n"
                                                 "</SigningPublicKey><EncryptionPublicKey>-----BEGIN PUBLIC KEY-----\n"
                                                 "-----END PUBLIC KEY-----\n"
                                                 "</EncryptionPublicKey></GeneralPurposePublicKey>");
      } catch (VHUtil::Exception &e) {
         f_threw_correct_exception = (e.getResultId ().find ("DSA_KEY_PARSING_ERROR") != e.getResultId ().npos);
      }
      CuAssert (tc,
                "Failed to notice bad public key",
                f_threw_correct_exception);
   }

   void sig_from_wrong_key (CuTest *tc)
   {
      // Similarly, ensure that a "good" signature -- but made with
      // the wrong private key -- gets detected.
      
      bool f_threw_correct_exception = false;
      {
         auto_freeing<ConstCharStar> signed_blob = 0;
         CuAssert (tc,
                   "VHTI_sign_xml unexpectedly failed",
                   !VHTI_sign_xml (good_private_key.c_str (),
                                   "<" BIG_GAMMA "/>",
                                   &signed_blob));

         // I usually don't like to hard-code test data, but in this
         // case, it doesn't make life any harder, and in fact it
         // lets the test run *much* faster than if we had to
         // regenerate a key pair.
         const char new_pub[] = 
            "<GeneralPurposePublicKey><IdentInfo>Mon Oct 20 11:30:49 2003</IdentInfo><SigningPublicKey>-----BEGIN PUBLIC KEY-----\r\n"
            "MIIBtzCCASwGByqGSM44BAEwggEfAoGBAKkW+MmrrlESWwFErr4HFV54881QaltD\r\n"
            "SyNxdPN+fYdfvPMNaAWcJZ+JhKaDQgB5xgBoEV3Zs4/uxpU7HdBzdSAJTKZXnUdL\r\n"
            "2bId/0EfLGwuF9v1MysV25Frclf9XyxAovuyDBbs/Wcm9iZiYnxcHICiaEjs/lJ5\r\n"
            "zSszGV8M4JAzAhUAimY811YsSDNy+Hbp8RICXGJi9SECgYEAmbtkg8YrfDsTykeG\r\n"
            "qDwIj1QHOla/Nd3gFxM9McEHkmsJcPSrbGZScW5jvhr/r+JaeEr2p5OYUBTOb5wK\r\n"
            "NK8F1efWYRL4C4ezeN4MzrIFk8WAGjyl/879JuxnjBn0YpD5pJ/9U+++SQs2MTnu\r\n"
            "l+yiS4OsZ3bjOBFKRY7mgsYgy9cDgYQAAoGAMiI/OdTxsnEq5m6uRG/Rw7XuD4FV\r\n"
            "YbAcSzePNR8Nw7GFnuvqGM9Vj1bd7d3bEWLy+gbhe+HM3Nzhdm0lrKpq+RySrVDD\r\n"
            "Gbogmu1HaLsf9vUfogO83PUO3WiZYvRSgBucLgSGriokFAYkBzj2tOboB5jvqVYE\r\n"
            "RM7GXGB4KORu/t8=\r\n"
            "-----END PUBLIC KEY-----\r\n"
            "</SigningPublicKey><EncryptionPublicKey>-----BEGIN PUBLIC KEY-----\r\n"
            "MIGdMA0GCSqGSIb3DQEBAQUAA4GLADCBhwKBgQDe92ihgB5XmiyT45PqiBO70wEL\r\n"
            "5+/dL1021wgOB4hI0wvXhpafju2hB/RoAR9K7oIEKl/G/U6mwSDjg8WbxXZg+4q7\r\n"
            "r+PcZWoKDFB+9If2klg+2mivVd0RRaA8LuQ/itNPqmsbsecgoluuvAv4f853S/E9\r\n"
            "uud6r9RfkN/2qKe6ZwIBAw==\r\n"
            "-----END PUBLIC KEY-----\r\n"
            "</EncryptionPublicKey></GeneralPurposePublicKey>";

         try {
            VHUtil::safe_xml_tree should_not_exist (static_cast<const char *> (signed_blob),
                                                    BIG_GAMMA,
                                                    new_pub);
         } catch (VHUtil::Exception &e) {
            f_threw_correct_exception = (e.getResultId ().find (CHECK_FAILURE_TEXT) != e.getResultId ().npos);
            if (!f_threw_correct_exception)
               std::cerr << "Wanted " << CHECK_FAILURE_TEXT << " but got " << e.getResultId () << std::endl;
         }
         CuAssert (tc,
                   "Failed to notice that signature was from wrong key",
                   f_threw_correct_exception);
      }
   }
   
   // Tests that the ctor actually does validity checking.
   void signed_invalid (CuTest *tc)
   {
      bool f_threw_correct_exception = false;
      VHUtil::xml_tree invalid_vrd_tree ("<" BIG_GAMMA "/>");
      invalid_vrd_tree.root ()->new_element ("bogus");

      VHUtil::xml_tree signed_tree ("<Signed" BIG_GAMMA "/>");
      signed_tree.root ()
         ->new_element (SIGNED_DATA)
         ->add_characters (invalid_vrd_tree);

      auto_freeing<Signature> signature = 0;
      VHTI_sign (good_private_key.c_str (),
                 invalid_vrd_tree.str ().c_str (),
                 &signature);
      signed_tree.root ()->new_element (SIGNATURE)->add_characters (VHUtil::xml_tree (static_cast<const char *>(signature)).root ()->characters ());

      try {
         VHUtil::safe_xml_tree should_not_exist (signed_tree.str ().c_str (),
                                                 BIG_GAMMA,
                                                 good_pub_key);
      } catch (VHUtil::Exception &e) {
         f_threw_correct_exception = (e.getWhat ().find ("INVALID_XML") != e.getWhat ().npos);
      }
      CuAssert (tc,
                "failed to notice invalid XML",
                f_threw_correct_exception);
   }

   void signed_unexpected_root (CuTest *tc)
   {
      bool f_threw_correct_exception = false;
      VHUtil::xml_tree ok ("<" BIG_GAMMA "/>");

      try {
         VHUtil::safe_xml_tree should_not_exist (ok.str ().c_str (),
                                                 "MaximumBogosity",
                                                 good_pub_key);
      } catch (VHUtil::Exception &e) {
         f_threw_correct_exception = (e.getWhat ().find ("INVALID_XML") != e.getWhat ().npos);
      }
      CuAssert (tc,
                "failed to notice mismatch between expected and actual root element names",
                f_threw_correct_exception);
   }

   void unsigned_invalid (CuTest *tc)
   {
      bool f_threw_correct_exception = false;
      try {
         VHUtil::safe_xml_tree invalid ("<" BIG_GAMMA "><bogus/></" BIG_GAMMA ">",
                                        BIG_GAMMA);

      } catch (VHUtil::Exception &e) {
         f_threw_correct_exception = (e.getWhat ().find ("INVALID_XML") != e.getWhat ().npos);
      }
      CuAssert (tc,
                "failed to notice invalid XML",
                f_threw_correct_exception);
   }

   void unsigned_unexpected_root (CuTest *tc)
   {
      bool f_threw_correct_exception = false;
      try {
         VHUtil::safe_xml_tree ok ("<" BIG_GAMMA "/>",
                                   "BoGussssssssssssssss");

      } catch (VHUtil::Exception &e) {
         f_threw_correct_exception = (e.getWhat ().find ("INVALID_XML") != e.getWhat ().npos);
      }
      CuAssert (tc,
                "failed to notice mismatch between expected and actual root names",
                f_threw_correct_exception);
   }
}

int main ()
{
   try {
      good_pub_key     = VHUtil::file_contents ("../../examples/ballot-signing-pubkey.xml");
      good_private_key = VHUtil::file_contents ("../../examples/ballot-signing-prvkey.xml");

      CuString *output = CuStringNew();
      my_suite = CuSuiteNew();

      SUITE_ADD_TEST(my_suite, not_XML);
      SUITE_ADD_TEST(my_suite, accepts_UTF_8);
      SUITE_ADD_TEST(my_suite, accepts_Latin_1);
      SUITE_ADD_TEST(my_suite, validates_valid_UTF_8);
      SUITE_ADD_TEST(my_suite, deep_copy_works);
      SUITE_ADD_TEST(my_suite, all_canon_tests);

      SUITE_ADD_TEST(my_suite, safe_xml_tree);
      SUITE_ADD_TEST(my_suite, sig_from_wrong_key);
      SUITE_ADD_TEST(my_suite, signed_invalid);
      SUITE_ADD_TEST(my_suite, signed_unexpected_root);
      SUITE_ADD_TEST(my_suite, unsigned_invalid);
      SUITE_ADD_TEST(my_suite, unsigned_unexpected_root);

      //libxml versions 2.2.11 through 2.5.4 (and possibly other
      //versions) dump core when we call this test.  So until we start
      //using a better version, we skip this test.

      //SUITE_ADD_TEST (my_suite, notices_invalid_UTF_8);

      CuSuiteRun (my_suite);
      CuSuiteSummary (my_suite, output);
      CuSuiteDetails (my_suite, output);
      std::cout << output->buffer << std::endl;
   } catch (VHUtil::Exception &e) {
      std::cerr << "Exception: " << e.what () << std::endl;
      return 2;
   }
   return (my_suite->failCount
           ? 1
           : 0);
}
