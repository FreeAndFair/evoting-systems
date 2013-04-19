The liquid_feedback_patch and how LQFB interacts with Solon
===========================================================

The below text is supposed to explain how the patch in liquid_feedback_patch/
works, and how Solon and Liquid Feedback (LQFB) interact.


Introduction
------------

Cryptographic voting algorithms are complex things and not something I
would try to implement in PLSQL.  (For one thing, they usually require
you to operate multiple servers operated by independent entities, with
network communication between.) So the patch in liquid_feedback_patch/ is simply 
about inserting necessary hooks where control flow is deviating to an
external system from the current LQFB core. Basically when an issue gets 
to voting phase, the accepted initiatives would be exported to the external 
system, and when voting time is over it will simply insert the results back into
battle table. Before and after these points everything would work as before.


Justification
-------------

I think current users of LQFB are probably best off with the simple,
unencrypted voting that is provided in core.sql 2.0. For instance, it
is not unreasonable to say that if you are active within the Pirate
Party you will in any case make your political opinions known to
everyone else.

Otoh I think that long term, when the use of systems like LQFB become
more significant, it is important to a) guarantee voter privacy as in
all modern western elections and b) guarantee the integrity of the
voting result. The latter point should be of concern even to the
existing usage of LQFB: Now the results of an LQFB vote can be
trivially tampered with by the DBA. Personally, I think it is likely
that this kind of liquid democracy system will spread to be used also
by local and maybe even state/national governments in some form,
either as binding referenda or in some soft-binding form. In such a
case - when there is a real decision at stake - I think voters deserve
guarantees that the voting is as secure as modern paper-ballot
elections.


About cryptographically secure voting algorithms
------------------------------------------------

From LQFB point of view the cryptographically secure voting happens
externally to LQFB, it is a black box and could use any algorithm. In Solon 
we want to implement the voting algorithm invented by Alessandro Acquisti: 
http://www.heinz.cmu.edu/~acquisti/papers/acquisti-electronic_voting.pdf

How to use this algorithm with a) a preferential voting method and b)
including vote delegation is not obvious from the above paper. Most
crypto research into voting system is of course focusing on solving
the problem of existing elections. I will explain my thoughts on how
to use the algorithm for the kind of voting seen in LQFB separately,
as we develop that system. Note that for the purpose of the
liquid_feedback_patch, the external system is considered a black box, and
could implement any voting algorithm.

Further reading: The Acquisti scheme has been implemented as a Masters
Thesis work, reported on here:
http://www.seas.upenn.edu/~cse400/CSE400_2004_2005/34writeup.pdf
...but of course the students did not save their code!

An overview and comparison of existing research into voting algorithms
is given in:
http://www.ee.washington.edu/research/nsl/papers/JCS-05.pdf

The last paper is a great intro if you are interested in this topic in general.

For clarity: Note that I am here talking about cryptographic secure
voting algorithms. This is an orthogonal issue to the use of condorcet
or schulze voting method, which are algorithms for counting a winner
from the votes. (Although, some cryptographic algorithms will not be
able to support an arbitrary voting method, such as preferential
voting.)


High Level Overview of the planned System
-----------------------------------------

A user may cast both a public vote and a private (secret) vote.

A public vote is the same as already exists in LQFB and is stored in
the database just as votes are stored now. Public votes *do not count*
as actual votes, but they are only used for the delegation of other
voters votes.

The private vote is each voters actual vote. It can be a vote directly
on the issue (ie an ordered list of the initiatives) or it can be a
vote on another person in the system - ie a delegated vote. For the
actual voting result, only these private votes are counted with a
value of "1" each. A private vote containing a delegation is counted
for whatever initiative the trustee has given his public vote to. As
is already the case in LQFB 2.0 the trustee may of course also have
delegated his vote to a third person in the system, and so on, in
which case the chain is followed to the end.

The public votes are therefore needed, because:
 - we cannot know the trustee's private vote, so counting delegated
votes would be impossible
 - we could not prevent circles in a delegation chain if the chain is not public
 - it is analogous to how elections work today: My vote in an election
is secret, however how the elected MP votes in his daily work in
parliament is public. The truster has the right to know how the
trustee voted.

The external system must also allow a voter to delegate his vote to a
trustee for all future issues - just like in LQFB 2.0. This is a
requirement on the external system and there's nothing in the patch
related to this.

A frontend will therefore have to support:
 - ability to cast public votes pretty much like now
 - ability to cast private votes toward the external system, ie new UI
elements and sending the vote over HTTP
 - in practice the frontend needs to support its share of
cryptographic operations executed *on the client* (ie the browser)
This is analogous to how encrypted email is only secure if you use
your own email client, but would be pointless if you use gmail from
the browser, since you would then have to give google your encryption
key. The client side functionality can be implemented in javascript, a
java applet, android code, etc...

The time to cast public votes is shorter than or equal to the time to
cast private votes. The rationale for having a shorter time to cast
the public votes is that if Alice wishes to delegate her vote to Bob,
then Alice can already see how Bob has voted (the public vote) when
she casts her vote at the later time. All cryptographic voting
algorithms do not allow it, but the Acquisti algorithm would also
allow Alice to cast a new vote, if she had first delegated her vote to
Bob at an early time, but then sees that Bob didn't vote as she
expected and therefore wants to change her vote.

The various ways of supporting and opposing initiatives and drafts in
the discussion phase remain completely public and are not altered by
the patch.



Description of the attached patch
---------------------------------

There is a new column system_setting.ext_voting_service. When this is
FALSE or NULL, everything works as without this patch. When it is TRUE, 
the system works as described next.

The TYPE issue_state has 2 new states: public_voting_closed and
private_voting_closed. These become part of the lifecycle of an issue
like this:

 (various drafting states) -> voting -> public_voting_closed ->
private_voting_closed -> calculation -> closed

The drafting stages of issues are unchanged and voting state is
entered just like until now. The external system will poll the event
table, and when noticing that an issue has entered this state, it will
retrieve the issue and its accepted initiatives and make its
preparations so that voters can start voting for them.

public_voting_closed is entered after policy.public_voting_time (a new
column) is elapsed. After this point the external system can retrieve
all public votes, which are needed to count result of delegated votes.
Note that the code that counts votes from table "vote" and collects
sums into table "battle" is *not* executed in this mode. This is
therefore as far as it goes for the public votes.

private_voting_closed is entered after policy.voting is elapsed. Note
that voting is now closed, but results are not yet available. Rather
the external system can now start calculating them. (This can be a
heavy operation and take at least minutes, depending on the algorithm
and voting population.) When ready, it inserts results of the voting
into battle table in the same format that LQFB does today. This is
taking into account results of the private votes plus all delegation
chains via public votes.

calculation is entered when the external voting system calls a new
function ext_results_available(). Basically, this just marks the issue
ready for the next step, which is usually triggered by lf_update (as
usual).

calculation -> closed is as before, it is entered when core.sql code
has finished calculating schulze ranks and determined the winner (if
any) of the vote.

As a by product the patch also improves test.sql a little: It now does 
the same tests for both system_setting.ext_voting_service=FALSE and =TRUE. 
To achieve this most of the existing code is now in the function issue_test() 
and the code is fixed so that it works also when sequences do not start
from 1. (Ie you can call it twice in a row and it will also work the
second time.)

As a fix unrelated to Solon or secure voting, the patch also adds a 
new function verify_results(). It happened that code would
pass testing because the code had no sql errors, but the end state
was still incorrect. Calling verify_results() should now catch such errors.
This functionality should be useful for all LQFB developers regardless of 
everything else.