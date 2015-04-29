#this is utils for the tests and not a test of utils.py

import site; site.addsitedir("/home/jimmy/tevs") #XXX
from Ballot import *
import logging
import sys

class _const(object):
    pass

sys.modules["const"] = _const()

def NilXtnz():
    return Extensions(
        transformer=lambda *_: lambda x, y: (x,y),
    )

def CONCHO(*a):
    """each arg is a contest, a list of x,y,w,h, a description; and a
    list of contests, given by a list of x,y, a description, bools of:
    was voted, iswritein, isambiguous, and an optional stats obj. The
    extra information is so we can compare with the [VoteInfo] results.
    CONCHO(
        (x,y,w,h, "prop", "description",
            (x, y, "desc", True, False, True),
            etc...
        ),
        etc...
    )
    returns the data required by the last arg of Page.as_template and
    a list of just the choices for easy comparison against votedata
    """
    ret, all = [], []
    for n in a:
        con = Contest(*n[:6])
        if len(n) < 7:
            continue
        for c in n[6:]:
            cho = Choice(*c[:3])
            #patch in extra info for concho_vs_vd to read
            cho.cd = n[5]
            cho.v, cho.wi, cho.a = c[3:6]
            #set stats if available
            cho.ss = None if len(c) < 7 else c[6]
            con.append(cho)
            all.append(cho)
        ret.append(con)
    return ret, all

def concho_vs_vd(chos, vds):
    """Takes the second return of CONCHO and the ballot results and
    makes sure everything is the same"""
    ret = True
    for ch, vd in zip(chos, vds):
        if any((
                len(ch.cd)     -  len(vd.contest) >= 5,
                ch.v           != vd.was_voted,
                ch.wi          != vd.is_writein,
                ch.a           != vd.ambiguous,
                len(ch.description) - len(vd.choice) >= 5,
                ch.x           -  vd.coords[0] >= 3,
                ch.y           -  vd.coords[1] >= 3,
                not stats_cmp(ch.ss,  vd.stats)
            )):
            print
            print ch.cd,":"
            if ch.cd != vd.contest:
                print vd.contest
            for l,a,b in (
                    ("voted",ch.v,vd.was_voted),
                    ("wrin",ch.wi,vd.is_writein),
                    ("ambig",ch.a,vd.ambiguous),
                    ("desc",ch.description,vd.choice),
                    ("x",ch.x,vd.coords[0]),
                    ("y",ch.y,vd.coords[1])):
                if a != b:
                    print l, a, b
            if ch.ss is not None:
                print "stats", stats_cmp(ch.ss, vd.stats)
            ret = False
    return ret

def stats_cmp(a, b):
    if a is None: #ie, we don't care about this
        return True
    return all(x != xp for x, xp in zip(a, b))

