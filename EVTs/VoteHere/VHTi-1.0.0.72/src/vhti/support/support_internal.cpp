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

#include <support/support_internal.h>
#include <support/mutex.h>
#include <util/sslerror.h>
#include <misc/safe_xml_tree.h>
#include <string>
#include <sstream>

namespace VHInternal {
   VHUtil::Mutex g_mutex(47);
};

#if defined (MOD_EXP_STATS)
#include <ctime>
namespace {
   clock_t time_spent_in_fme = 0;
   clock_t time_spent_in_BN_mod_exp = 0;
}
void
dump_stats()
{
   VHUtil::cout() << "fixed_mod_exp spent "
                  << (double) time_spent_in_fme / CLOCKS_PER_SEC
                  << " seconds, whereas BN_mod_exp spent "
                  << (double) time_spent_in_BN_mod_exp / CLOCKS_PER_SEC
                  << " seconds."
                  << std::endl;
}

#endif

namespace {

   typedef std::pair< auto_BN, auto_BN > g_base_mod_pair;
   typedef std::vector< auto_BN > g_bn_vec;
   std::map< g_base_mod_pair, g_bn_vec > g_fme_map;
}

namespace VHInternal {

void
check_group_membership (auto_BN & input_val,
                        auto_BN & pm,
                        auto_BN & qm)
{
   int result = 0;
   auto_BN_CTX ctx(BN_CTX_new());
   if (!ctx)
      throw SSL_ERROR;

   auto_BN testval;
   if (!BN_mod_exp(testval, input_val, qm, pm, ctx))
      throw SSL_ERROR;

   VH_nonzero (BN_is_one (testval), NOT_SUBGROUP_MEMBER);
}

void
fixed_mod_exp (auto_BN & retval,
               const auto_BN & base,
               const auto_BN & exp,
               const auto_BN & modulus,
               auto_BN_CTX & ctx)
{
#if defined (MOD_EXP_STATS)
   clock_t start_time = clock();
#endif

   // Number of bits in the exponent
   int numbits = BN_num_bits(exp);

   // An iterator to search the map
   std::map< g_base_mod_pair, g_bn_vec >::iterator m_it;
   // The values corresponding to our base
   g_bn_vec current_vector;
   // Try to find base in map

   VHUtil::AutoMutex m(g_mutex);
   m_it = g_fme_map.find(g_base_mod_pair(base, modulus));
   {
      // Make a mutex object to keep the map in one thread at a time

      if (m_it != g_fme_map.end() )
      {
         // Found it
         current_vector = m_it->second;
         if (current_vector.size() < numbits )
         {
            // Need more bits in the vector
            for (int n=current_vector.size(); n<numbits; n++)
            {
               // The final table value
               auto_BN t_value;
               if ( !(BN_mod_mul(t_value, current_vector[n-1], current_vector[n-1],
                  modulus, ctx)) )
                  throw SSL_ERROR;
               current_vector.push_back(t_value);
            }
         }
      }
      else
      {
         // Didn't find it, create the table values and put into a new vector
         std::vector< auto_BN > table_values;
         // Seed our table with the base^(2^0)
         table_values.push_back(base);

         for (int i=1; i<numbits; i++)
         {
            // The final table value
            auto_BN t_value;
            if ( !(BN_mod_mul(t_value, table_values[i-1], table_values[i-1],
               modulus, ctx)) )
               throw SSL_ERROR;
            table_values.push_back(t_value);
         }
         current_vector = table_values;
         // Add the base and vector to our map
         g_fme_map.insert(std::pair< g_base_mod_pair, g_bn_vec >
            (g_base_mod_pair(base, modulus), current_vector));
      }
   }

   // Now look up the exponent
   // Our running product
   auto_BN prod_values;
   BN_one(prod_values);
   for (int j=0; j<numbits; j++)
   {
      // Find out which bits are set, then find those
      // values in the vector and multiply them together
      if (BN_is_bit_set(exp, j) != 0)
      {
         // The bit is set, so find the value in the vector and multiply
         if ( !(BN_mod_mul(prod_values, prod_values, current_vector[j], modulus, ctx)) )
            throw SSL_ERROR;
      }
   }

   retval = prod_values;

#if defined (MOD_EXP_STATS)
   time_spent_in_fme += clock() - start_time;

   {
      auto_BN alternate_retval;
      clock_t start_time = clock();
      BN_mod_exp(alternate_retval, base, exp, modulus, ctx);
      time_spent_in_BN_mod_exp += clock() - start_time;
      VH_zero(BN_cmp(alternate_retval, retval), FIXED_MOD_EXP_SCREWED_UP);
   }
#endif
}

void
get_election_parameters
(const std::string &input,
 auto_BN & pm,
 auto_BN & qm,
 auto_BN & gen,
 auto_BN & ePublicKey)
{
   VHUtil::xml_tree xml_input(input);
   VHUtil::xml_node root = xml_input.root ();
   get_election_parameters2(root, pm, qm, gen, ePublicKey);
}

void
get_election_parameters2 (VHUtil::xml_node &xml_input,
                          auto_BN & pm,
                          auto_BN & qm,
                          auto_BN & gen,
                          auto_BN & ePublicKey)
{
   VHUtil::xml_node node_crypto_params = NULL;
   VHUtil::xml_node node_tab_params = NULL;
   
   if (xml_input->name() == "BlankBallot")
   {
      node_crypto_params = xml_input
         ->e(CRYPTO_ELECTION_PARAMETERS)->e(CRYPTO_GROUP_PARAMETERS);
      
      node_tab_params = xml_input
         ->e(CRYPTO_ELECTION_PARAMETERS)->e(CRYPTO_TABULATION_PARAMETERS);
   }
   else if (xml_input->name() == CRYPTO_ELECTION_PARAMETERS)
   {
      node_crypto_params = xml_input->e(CRYPTO_GROUP_PARAMETERS);
      
      node_tab_params = xml_input->e(CRYPTO_TABULATION_PARAMETERS);
   }
   else if (xml_input->name() == CRYPTO_GROUP_PARAMETERS)
   {
      node_crypto_params = xml_input;
   }
   else
      VHUtil::_assert("UNKNOWN_ELEMENT", __FILE__, __LINE__);

   pm = xml2BN(node_crypto_params->e(ELECTION_MODULUS));
   qm = xml2BN(node_crypto_params->e(ELECTION_SUBGROUP_MODULUS));
   gen = xml2BN(node_crypto_params->e(ELECTION_SUBGROUP_MEMBER));
   if (node_tab_params != NULL)
   {
      ePublicKey = xml2BN( node_tab_params->e(ELECTION_PUBLIC_KEY));
   }
}

long int
str2num (const std::string &s,
         const std::string &error_message)
{
   return read_int (std::istringstream (s),
                    error_message);
}

long int
read_int (std::istream &s,
          const std::string &error_message)
{
   long int rv = 0;
   s >> rv;
   if (!s)
      VHUtil::_check (("MALFORMED_INTEGER " + error_message).c_str (), __FILE__, __LINE__);

   return rv;
}

long int
int_from_attribute (VHUtil::xml_node n,
                    const std::string &attribute_name)
{
   std::ostringstream whine;
   const std::string attr_value = n->attribute (attribute_name);
   whine << "On node `"
         << n->name ()
         << "', value of attribute `"
         << attribute_name
         << "' is not an integer: `"
         << attr_value
         << "'";
   return (str2num (attr_value,
                    whine.str ()));
}

long int
int_from_characters (VHUtil::xml_node n)
{
   std::ostringstream whine;
   const std::string chars = n->characters ();
   whine << "Characters of node `"
         << n->name ()
         << "' do not form an integer: `"
         << chars
         << "'";
   return (str2num (chars,
                    whine.str ()));
}

}
