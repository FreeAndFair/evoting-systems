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

#include <vhti/types.h>
#include <support_test/test-data.h>

const char *const invalid_pubkey = "<" IDENT_INFO " />";
const char *const invalid_prvkey = "<" IDENT_INFO " />";
const char *const invalid_encrypted_data = "<" IDENT_INFO " />";
const char *const invalid_ident_info = "<snurkly />";
const char *const invalid_keytype = "<" IDENT_INFO " />";
const char *const invalid_signed_document = "<" IDENT_INFO "/>";
const char *const invalid_password = "<" IDENT_INFO "/>";
const char *const invalid_pw_encrypted_data = "<" IDENT_INFO "/>";

const char *valid_pubkey =
"<GeneralPurposePublicKey>"
"<IdentInfo>Mr. Michael Mouse</IdentInfo>"
"<SigningPublicKey>"
"-----BEGIN PUBLIC KEY-----\r\n"
"MIIBtjCCASsGByqGSM44BAEwggEeAoGBAMLKWrrN9lBmVHmO0tVs0WFlXmIEqLo2\r\n"
"xT8zrgcBi2Xe0IrBHmgBoqO/kUFhyeXBwMUu8GAao0ujtbxEi1hxAHEFJulqeNkd\r\n"
"eq/4Nf+/VhdH/QwSGeabp2fujxEZ16UesEAgrDYVZowqYtRlSmCtqa1Rm3MfRPHp\r\n"
"PoT4V2s7PLnpAhUA63nE7PeruCv9qOrLAMPzhO86HVECgYB5CL7Ahc5McpYTFqLf\r\n"
"wKTB9zr3oFfsFRn4sQwb6qKuF5o6i4AnWc2DAwH4VKujKoNBxUQj7HXEzvicn3nc\r\n"
"73MQeWGFX9g6GLGG0EW/SRtQqbWZGqW5HI6Wv4Qoo5VCzrg3D2QVkJEFSo0ESEUR\r\n"
"tXebUXSDmeGP5cldUa9fFuaKcQOBhAACgYAVN/1BQ/OvWzybmKg95Ra5/mbkmCAL\r\n"
"JzozZmP79t7uW0h3zxYzxhXke8a265SI67fVWlfbqqZ8R4GXan6K5no5wq8bBhGi\r\n"
"FhkOkvScl/mnTmxOw01bqTAlppOL4z8ClZAvZizHklWYuWFrI63/bvlv7Hu+4EbD\r\n"
"FOxM9n/9xWNN0w==\r\n"
"-----END PUBLIC KEY-----</SigningPublicKey>" 
"<EncryptionPublicKey>"
"-----BEGIN PUBLIC KEY-----\r\n"
"MIGfMA0GCSqGSIb3DQEBAQUAA4GNADCBiQKBgQDXKDOk1YbdWbx9agJcssSpsrxW\r\n"
"2WRn6WCj3dpxK4L8w70+muj91cPfV461aC8GM/bji4bcp7Xj6ijCQUYWjtsxL0JQ\r\n"
"dHjSg37Z4p8d1KqCFRIbOARnylqmicclpbTSlJsR6091FM25ZXuRFufn+oX59Log\r\n"
"uImkqId3VBUoz3nRVwIDAQAB\r\n"
"-----END PUBLIC KEY-----</EncryptionPublicKey>"
"</GeneralPurposePublicKey>";

const char * valid_prvkey =
"<GeneralPurposePrivateKey>"
"<IdentInfo>Madam Blavatsky</IdentInfo>"
"<SigningPrivateKey>"
"-----BEGIN DSA PRIVATE KEY-----\r\n"
"MIIBuwIBAAKBgQDCylq6zfZQZlR5jtLVbNFhZV5iBKi6NsU/M64HAYtl3tCKwR5o\r\n"
"AaKjv5FBYcnlwcDFLvBgGqNLo7W8RItYcQBxBSbpanjZHXqv+DX/v1YXR/0MEhnm\r\n"
"m6dn7o8RGdelHrBAIKw2FWaMKmLUZUpgramtUZtzH0Tx6T6E+FdrOzy56QIVAOt5\r\n"
"xOz3q7gr/ajqywDD84TvOh1RAoGAeQi+wIXOTHKWExai38Ckwfc696BX7BUZ+LEM\r\n"
"G+qirheaOouAJ1nNgwMB+FSroyqDQcVEI+x1xM74nJ953O9zEHlhhV/YOhixhtBF\r\n"
"v0kbUKm1mRqluRyOlr+EKKOVQs64Nw9kFZCRBUqNBEhFEbV3m1F0g5nhj+XJXVGv\r\n"
"XxbminECgYAVN/1BQ/OvWzybmKg95Ra5/mbkmCALJzozZmP79t7uW0h3zxYzxhXk\r\n"
"e8a265SI67fVWlfbqqZ8R4GXan6K5no5wq8bBhGiFhkOkvScl/mnTmxOw01bqTAl\r\n"
"ppOL4z8ClZAvZizHklWYuWFrI63/bvlv7Hu+4EbDFOxM9n/9xWNN0wIVAJx4Vilt\r\n"
"Ue7GefXUPwPCdeBYzlfD\r\n"
"-----END DSA PRIVATE KEY-----</SigningPrivateKey>"
"<EncryptionPrivateKey>"
"-----BEGIN RSA PRIVATE KEY-----\r\n"
"MIICXAIBAAKBgQDXKDOk1YbdWbx9agJcssSpsrxW2WRn6WCj3dpxK4L8w70+muj9\r\n"
"1cPfV461aC8GM/bji4bcp7Xj6ijCQUYWjtsxL0JQdHjSg37Z4p8d1KqCFRIbOARn\r\n"
"ylqmicclpbTSlJsR6091FM25ZXuRFufn+oX59LoguImkqId3VBUoz3nRVwIDAQAB\r\n"
"AoGABNsEZ1jmRUKMLWxiB0OFiqrc8zzOtkWfB7OvBVTNDPVB5RLL5UaYuAaa0t86\r\n"
"CHLNxI7WiU5DnZQgPVoJweKRcb0U3SRrmSQQUVDcXON24pnqKdF76/M7uxWPjcIS\r\n"
"seC69/nWowbTNg21IoMOPI52EJv1J7Sl+ExkWdikhvudb1ECQQD/VRdUiLY1ovML\r\n"
"PCtFIlsBz0PiQOazdgjwbKpryXvrHAJAWkNJowJB276cIqtEciSrkGUBs8B9LPRv\r\n"
"0k6tkuU/AkEA17g4CXstf6Eolar/DZSaj5SV99IkSVFC2XWZ7YIbvOiyZ92teRTB\r\n"
"BPRs18Nmem1O9tAhhm0uXL6waldXbMcV6QJBALnA784h/10aBPMBfQE4szinzt0F\r\n"
"FlEs5+fxRjJQTISIxeKHSDiEDJpZAVyZpDuRRrhBvhn06W6ni9TmDTMdkQUCQDOa\r\n"
"GKWD9q1KIsgyoFJiUtq3w2wFs7JqIuCb9hdPgU0eKNcZuw50vXtu8L5oOpJcpX/6\r\n"
"55odcfKzlsXJYNtfgEkCQGwamqLZ+1G5RsUfCSFIJPhvYgGpwWx2jiVlNjdl1yTK\r\n"
"tLNiFBa/muN5J3dI+hxE2miR5i19LALPwLv1FQR2T4g=\r\n"
"-----END RSA PRIVATE KEY-----</EncryptionPrivateKey>"
"</GeneralPurposePrivateKey>";

const char *const valid_non_XML_plaintext = "Hello World!!  Lookit me -- I'm not XML!!";
const char *const valid_XML_plaintext = "<" VOTE_RECEIPT_DATA "/>";

const char *const valid_signature = "<?xml version=\"1.0\"?>\n"
"<Signature>"
"MC4CFQDgTFU5+mZDzg4rMElcYLiM9geE0gIVAM1NuS/raZ45zW+BV92f3g/Wrghx"
"</Signature>";

const char *const valid_ident_info = 
"<IdentInfo>"
"some info"
"</IdentInfo>";

const char *const valid_password = "<Password>Shhhh</Password>";

const char *const valid_pw_encrypted_data =
"<PasswordEncryptedData>"
"<CipherText>ni6R/xAWmqA2G0tM5tR7e5MVdfdsturq5BZyy1BjkPo=</CipherText>"
"</PasswordEncryptedData>";
