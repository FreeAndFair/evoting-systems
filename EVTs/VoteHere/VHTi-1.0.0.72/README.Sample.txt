Samples

This release contains three slightly different sets of examples.  

In the src/examples/election_sample we have a set of bash and Perl scripts
that demonstrate a full election.  It is documented in
src/examples/election_sample/README.  When executed, this sample leaves all
of its data in various .xml files in the _sample_data directory.

In the src/bindings/perl/examples directory we have essentially the
same thing, but all in Perl.

In the src/examples directory we also have a set of other directories which
each contain a C++ sample.  These are buildable with Developer Studio and
allow stepping through the code with a debugger.

In addtion to the examples, we have some self-tests.  The
"run-all-tests.sh" script in the /src directory invokes them all (as
well as the examples), and is thus a good way to verify that your
build completed successfully.  Depending on your Cygwin installation,
it may be necessary to install extra Perl modules.  For information
about this, see http://www.cpan.org/

This material is subject to the VoteHere Source Code Evaluation
License Agreement (``Agreement'').  Possession and/or use of this
material indicates your acceptance of this Agreement in its entirety.
Copies of the Agreement may be found at www.votehere.net.

Copyright 2004 VoteHere, Inc.  All Rights Reserved
