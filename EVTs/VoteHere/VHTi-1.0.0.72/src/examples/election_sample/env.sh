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

# Environment
here=$(cd $(dirname $0); pwd)
export PERL5LIB=$here/../../vhti/bindings/perl:$here/../../vhti/bindings/perl/vhti_xs:$here/perl

# Make binding DLL
cd $here/../../vhti/bindings/perl
make -f perl.mk
make
cd $here

export LD_LIBRARY_PATH=$here/../../vhti/bindings/perl/:$here/../../vhti/bindings/perl/blib/arch/auto/VHTI_XS  # home of VHTI_XS.dll

PATH=$PATH:$here:$here/../../vhti/bindings/perl:$here/../../vhti/lib    # home of vhti_call & vhti_dll.dll

# Election parameters
export VHTI_ELECTION_SAMPLE_EID=12        # election id
export VHTI_ELECTION_SAMPLE_PID=4         # precinct id
export VHTI_ELECTION_SAMPLE_N=3           # number of trustees
export VHTI_ELECTION_SAMPLE_T=2           # trustee threshold
export VHTI_ELECTION_SAMPLE_NBSN=25       # number of blank ballots
export VHTI_ELECTION_SAMPLE_NBSNP=0       # number of provisional blank ballots

export VHTI_ELECTION_SAMPLE_VCBITS=16     # verification code bit length
