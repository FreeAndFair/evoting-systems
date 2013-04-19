Solon Voting
============
A cryptographically secure voting system for direct democracy platforms.

Introduction
------------

Solon is a system that provides cryptographically secure electronic voting 
(e-voting), particularly focusing on direct democracy platforms instead of
replicating the functionality of a classic representative democracy election.

Solon is designed to be used together with burgeoning direct democracy and 
delegated democracy systems. These typically have requirements that go beyond
your average parliamentary elections. In particular, the voting algorithm needs
to support the possibility to flexibly delegate (and un-delegate) your vote at
any time, and it must be possible to use more advanced vote counting, such as 
Schulze method and other preferential voting methods.

Currently, we focus on providing a cryptographically secure voting facility
that connects with [Liquid Feedback]. However, the code is modular in this
respect, and in the future we will be able to support any other similar system.
See "Direct democracy platforms" for other systems we like to keep an eye on.

[liquid feedback]: http://liquidfeedback.org/

After starting Solon we have become aware of an open source implementation of 
a so-called homomorphic e-voting algorithm: [Helios Voting]. The current focus
is on using Helios as the secure voting backend for Solon. Essentially this
means Solon acts as integration and orchestration layer between Liquid Feedback
and Helios. New issues to vote on are discovered in the Liquid Feedback 
workflow, the data is then copied into Solon and a Helios ballot is created.
Users will then vote securely using Helios, after which Solon will copy the
results back into Liquid Feedback.

[helios voting]: http://heliosvoting.org/

Status
------

Solon is currently in active development, and it is not ready to be used yet.

The current code is merely a mockup that is able to connect with a Liquid 
Feedback system, extract issues to vote on and return results back. It is just
a mockup that demonstrates the data flows. The actual code for any cryptographic
functionality is completely missing. Integrating with the Helios project is the
next step and proof of concept work for this is now in progress.

If you want to contribute to development, join us on [Github]! The Solon
developers think it's an exciting prospect to take representative democracy to
the next level, and if you feel the same, you are welcome to join. See 
"Contributing" below for more info.

[github]: https://github.com/henrikingo/solon-voting


Installation
------------

### Install Liquid Feedback

You need a working Liquid Feedback installation to use Solon. Not only that,
but you need a patched version of Liquid Feedback Core. Let's start with that.

We have tested the following versions of Liquid Feedback components:

LiquidFeedback Frontend  2.0.1
LiquidFeedback Core      2.0.11
WebMCP                   1.2.3
Lua                      5.1
PostgreSQL               8.4.12

Note that the Solon patch for Liquid Feedback is specifically against v2.0.11
of LiquidFeedback Core, and the Frontend version must match the version of Core
that you use. So for now those two must be exactly 2.0.11 and 2.0.1 
respectively.

0) Tip: Liquid Feedback supports Debian Squeeze. If you are on any other platform,
it's probably worth taking that seriously: try using Vagrant or VirtualBox to 
install Liquid Feedback into a Debian Squeeze instance.

1) Download Liquid Feedback Core 2.0.11. This is currently the only version
against which we provide a patch, newer versions will probably not work.
`wget http://www.public-software-group.org/pub/projects/liquid_feedback/backend/v2.0.11/liquid_feedback_core-v2.0.11.tar.gz`

2) Untar: `tar xvf liquid_feedback_core-v2.0.11.tar.gz` and 
`cd cd liquid_feedback_core-v2.0.11/`

3) Get the patch: `wget https://raw.github.com/henrikingo/solon-voting/liquid_feedback_patch/liquid_feedback_core-v2.0.11.solon-v0.1.diff`

4) `patch -p1 < liquid_feedback_core-v2.0.11.solon-v0.1.diff`

5) You can now follow the instructions from 
http://dev.liquidfeedback.org/trac/lf/wiki/installation to install the full
Liquid Feedback system. When it is time to install the Core module, use the
directory you have just patched with the Solon enabling patch.

Note that for the Liquid Feedback Frontend, version 2.0.1 has been tested!

6) Finally, you need to configure Liquid Feedback to run in the 
ext_voting_service mode so that Solon can hook into your voting procedure:

    su - www-data
    psql -c "INSERT INTO system_setting (member_ttl, ext_voting_service) VALUES ('1 year', TRUE);" liquid_feedback
    psql -c "UPDATE system_setting SET ext_voting_service=TRUE;" liquid_feedback
    exit

(Note that if the second command above fails, that's ok.)

You can now browse Liquid Feedback via a web browser. When you login as 
administrator, there's a very small "Admin" link at the bottom of the page. You
can use that to create new users and organizations and policies that are used
for issue management.

### Install Solon itself

Currently Solon is tested on

Python 2.7
Tornado 2.1

Tornado 1.x is known not to work.

7) Install a few Python modules that we need: `apt-get install python-tornado python-psycopg2`

8) `git clone https://github.com/henrikingo/solon-voting.git`

9) `cd solon-voting`

10) You need to create another PostgreSQL database to be used by Solon. (Note:
The current Solon is just a mockup without cryptography, so we call the module
"dummy" and hence we tend to use the database name "solon_dummy".) Here we use
the same user "www-data" as was used in the instructions for Liquid Feedback:

    su - www-data
    createdb solon_dummy
    createlang plpgsql solon_dummy
    psql -v ON_ERROR_STOP=1 -f sql/dummy.sql solon_dummy
    exit

11) Optionally, edit the configuration file `config.py`. (If you didn't change
anything in the above instructions, such as usernames or passwords, then you're
good to go and don't need to change anything in the config.)

12) Start the webserver: `su www-data -c 'python solon_server.py'`

Now you can open a web browser and go to localhost:8888. Hit the "execute cron 
tasks" link to see if you can fetch your first issues from Liquid Feedback to
vote on.


Contributing
------------

If you are exited about the prospect of taking representative democracy to the
next level, then you might be interested in joining us. Check out the code at
https://github.com/henrikingo/solon-voting 

Solon might be especially interesting if you are into cryptography or math. Even
if we can use a lot of the functionality directly from Helios (thanks to the 
wonders of open source!) in the long term we will have to extend it to make it
more robust for large scale, "important", voting. But the 
project isn't exclusive to math geeks! There are a number of skills from Python,
HTTP, JSON and automated testing where your help is welcome.

Please read the file [TODO.md] for an idea on tasks where contributions are 
especially welcome.

[TODO.md]: https://raw.github.com/henrikingo/solon-voting/master/TODO.md

The official project mailing-list is at solon-voting@googlegroups.com.
https://groups.google.com/forum/#!forum/solon-voting

You may also follow, and @mention or DM, [@SolonVoting] on Twitter.

[@SolonVoting]: https://twitter.com/solonvoting

Solon architecture and design decisions have been described on my blog at:
http://openlife.cc/category/topic/solon 


Reading list
------------

If you are interested in the concept of delegated democracy, here are a few 
links:

 * http://en.wikipedia.org/wiki/Delegative_democracy
 * http://liquidfeedback.org/mission/
 * http://openlife.cc/DirectDemocracy

As for crypto and e-voting algorithms, it makes sense to start by reading the 
[Helios Voting paper].

[helios voting paper]: http://www.usenix.org/events/sec08/tech/full_papers/adida/adida.pdf

Note: Unless you enjoy reading papers stuffed with university level math, some
of these links may not be for you. It is still possible to contribute to Solon
even if you don't want to torture your brain cells with the actual cryptography.
If you do enjoy university level math, brace yourself, because the good stuff
has just begun!

The next paper is a good overview of the field of cryptographic e-voting 
protocols and the requirements such a protocol should meet. Even if you don't 
want to read about the math involved, I recommend you read at least the 
beginning of this paper. The introduction in this paper is useful to everyone 
who want to get an overview of e-voting protocols:
[Sampigethaya et.al.]

[Sampigethaya et.al.]: http://www.ee.washington.edu/research/nsl/papers/JCS-05.pdf "A framework and taxonomy for comparison of electronic voting schemes, K Sampigethaya, R Poovendran, Computers & Security, Elsevier 2006."


The Sampigethaya paper concludes that one [Acquisti protocol] is the most 
complete solution (at the time of its writing, of course). Before finding the 
Helios project we were planning to implement Acquisti in Solon. You may still be 
interested to read about it as it is a concise and well written paper. (But
now this is only for math geeks :-)

[Acquisti]: http://www.heinz.cmu.edu/~acquisti/papers/acquisti-electronic_voting.pdf "Receipt-free Homomorphic Elections and Write-in Ballots, Alessandro Acquisti. Technical Report 2004/105, International Association for Cryptologic Research, May 2, 2004."

The following papers are commentaries on Acquisti: 

[Goulet et.al.] implemented Aquisti in software, graduated, didn't keep any 
copies and didn't publish it as open source:

[Goulet et.al.]: http://www.seas.upenn.edu/~cse400/CSE400_2004_2005/34writeup.pdf "Surveying and Improving Electronic Voting Schemes, Jonathan D. Goulet, Jeffrey S. Zitelli, Sampath Kannan, 2005."

The following papers reference the Acquisti paper and provide some critique. I
have not yet read them in detail myself: [Meng], [Meng2]

[Meng]: http://people.scs.carleton.ca/~clark/biblio/coercion/Meng%202010.pdf "A Receipt-free Coercion-resistant Remote Internet Voting Protocol without Physical Assumptions through Deniable Encryption and Trapdoor Commitment Scheme, Bo Meng, Zimao Li and Jun Qin. JOURNAL OF SOFTWARE, VOL. 5, NO. 9, SEPTEMBER 2010."
[Meng2]: http://www.academypublisher.com/proc/iscsct10/papers/iscsct10p148.pdf "Automatic Verification of Acquisti Voting Protocol in Formal Model, Bo Meng, Wei Huang, and Dejun Wang. Proceedings of the Third International Symposium on Computer Science and Computational Technology(ISCSCT ’10) Jiaozuo, P. R. China, 14-15,August 2010, pp. 148-150."


Direct democracy platforms
--------------------------

Initially, we focus on making Solon work together with [Liquid Feedback].

[liquid feedback]: http://liquidfeedback.org

These platforms also have some form of direct democracy or delegated democracy
potential in them:

 * [Popvox] (https://www.popvox.com/ "Popvox")

We might try to support them in the future, but for now it's just interesting
to keep an eye on how this area develops.

Frequently Asked Questions
--------------------------

See [docs/FAQ.md]

[docs/FAQ.md]: https://raw.github.com/henrikingo/solon-voting/master/docs/FAQ.md


LICENSE
-------

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <http://www.gnu.org/licenses/>.

