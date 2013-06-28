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

echo Build started at `date`

brunch_root=$(cd $(dirname $0)/..; pwd)

set -e

cd $brunch_root/src

for i in {vhti_dll,vhti_activex,_tests_and_samples}\ -\ Win32\ {Release,Debug}
  do
  msdev vhti.dsw /make "$i"
done


echo "Building Cygwin Perl extensions"

cd $brunch_root/src/vhti/bindings/perl
# This makes a makefile, and autogenerates magical stuff for the perl
# bindings.  The perl bindings aren't actually needed now (they are
# only needed for testing, and hence get built by
# ../development/run-all-tests.sh), but a side-effect of the process
# *is* needed: a file called "functions".
# Temporary displacement of using this...
#make -f perl.mk
perl ./Makefile.PL
make
make install
make clean
cd $brunch_root/src/vhti/bindings/perl_ole
perl ./Makefile.PL
make
make install
make clean

case $ACTIVESTATE_PERL in
  "")
      echo "Set ACTIVESTATE_PERL to the AS perl binary if you'd like to install the VHTI perl interfaces for AS."
      ;;
  *) 
      if [ -f $ACTIVESTATE_PERL ]; then
        echo "Building ActiveState Perl extensions"
        cd $brunch_root/src/vhti/bindings/perl
	  $ACTIVESTATE_PERL ./Makefile.PL
          nmake
          nmake install
	  nmake clean
        cd $brunch_root/src/vhti/bindings/perl_ole
          $ACTIVESTATE_PERL ./Makefile.PL
          nmake
          nmake install
	  nmake clean   
      fi
      ;;
esac

echo
echo You\'re going to run $brunch_root/src/run-all-tests.sh now, right?
