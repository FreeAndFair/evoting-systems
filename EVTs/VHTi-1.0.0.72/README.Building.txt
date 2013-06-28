-*-outline-*-
See doc/apiref/vhapidoc for prerequisites -- build machine OS,
third-party libraries, etc.

* Cygwin

Install *all* of Cygwin from http://www.cygwin.com/setup.exe.  At the
"Select Packages" screen, it'll show a tree view whose root node is
"All", with the word "Default" next to it.  Click on "Default" once;
it (and all the other "Defaults" below it in the tree) should change
to "Install".

It's true that you don't need all (or even most) of that stuff, but
it's much easier to just install all of it, than to wonder if a build
failure was caused by missing Cygwin stuff.  Just install it all.

Now (assuming you've installed in c:\cygwin) edit
c:\cygwin\cygwin.bat, and add this line before the line that invokes
"bash":

        set CYGWIN=tty

** ent

One of the perl tests requires `ent.exe', which you can download from
http://www.fourmilab.ch/random/random.zip.

** CPAN perl modules

Now do 

	perl -MCPAN -e "install Carp::Assert"

That will start a long, annoying interactive process in which you'll
have to answer a lot of questions.  As far as I remember, the only
ones where the defaults won't work are

- the one about "Policy on building prerequisites".  Type "follow".

- the one about which mirror to use.  Drill down until you get one
  that's networkologically nearby.
    
Similarly do
	
	perl -MCPAN -e "install XML::SAX"
	perl -MCPAN -e "install File::Slurp"
	perl -MCPAN -e "install Math::Pari"

These won't ask you nearly as many questions, although the last one
will ask permission to download the source of the Pari library; you
need to type "yes" or something to let it do so.

If you know what you are doing with XML::SAX, you can install the
SAX Expat interface, which will process XML much faster than the
default SAX parser.

* Visual Studio

Somewhat surprisingly, even if perl is on your path when you invoke
Visual Studio, VS may not find it, since it ignores your path!  So you
must explcitly tell it by clicking "Tools", "Options", "Directories",
"Executable Files", and adding the cygwin "bin" directory to the end
of the list.

* Actually building

Start a Cygwin bash shell, and run development/src/vhmake.sh.

* Testing

Run development/src/run-all-tests.sh.

** So did the tests pass, or not?

They all passed if and only if the exit status from run-all-tests.sh
is zero (i.e., `echo $?' displays `0'), despite any scary messages
that may have been printed out.


This material is subject to the VoteHere Source Code Evaluation
License Agreement (``Agreement'').  Possession and/or use of this
material indicates your acceptance of this Agreement in its entirety.
Copies of the Agreement may be found at www.votehere.net.

Copyright 2004 VoteHere, Inc.  All Rights Reserved
