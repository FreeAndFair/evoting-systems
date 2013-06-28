#!/bin/bash
# 
# This material is subject to the VoteHere Source Code Evaluation
# License Agreement ("Agreement").  Possession and/or use of this
# material indicates your acceptance of this Agreement in its entirety.
# Copies of the Agreement may be found at www.votehere.net.
# 
# Copyright 2004 VoteHere, Inc.  All Rights Reserved
# 
# You may not download this Software if you are located in any country
# (or are a national of a country) subject to a general U.S. or
# U.N. embargo or are deemed to be a terrorist country (i.e., Cuba,
# Iran, Iraq, Libya, North Korea, Sudan and Syria) by the United States
# (each a "Prohibited Country") or are otherwise denied export
# privileges from the United States or Canada ("Denied Person").
# Further, you may not transfer or re-export the Software to any such
# country or Denied Person without a license or authorization from the
# U.S. government.  By downloading the Software, you represent and
# warrant that you are not a Denied Person, are not located in or a
# national of a Prohibited Country, and will not export or re-export to
# any Prohibited Country or Denied Party.
set -e 

# Usage
if test $# -lt 2 ; then
   echo "Usage: cep2kgp.sh CRYPTOELECTIONPARAMETERS_XML_FILE KEYGENPARAMETERS_XML_FILE"
   exit 2
fi
cep=$1
kgp=$2

perl ../perl/extract_element.pl $cep ./__cgp.xml "CryptoGroupParameters"
perl ../perl/extract_element.pl $cep ./__ctp.xml "CryptoTabulationParameters"
perl ../perl/extract_element.pl ./__ctp.xml ./__n.xml "NumAuth"
perl ../perl/extract_element.pl ./__ctp.xml ./__t.xml "Threshold"

# Create KeyGenParameters
echo "<KeyGenParameters>" > $kgp
cat ./__cgp.xml >> $kgp
cat ./__n.xml >> $kgp
cat ./__t.xml >> $kgp
echo "</KeyGenParameters>" >> $kgp

# Clean-up
rm -f ./__*

