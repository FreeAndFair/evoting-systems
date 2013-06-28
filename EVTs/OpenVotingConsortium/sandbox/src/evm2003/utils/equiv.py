"""Compare ballot XML files for equivalence

This file may be imported as a module or used as a command-line ballot
comparison tool. If imported, e.g.:

    >>> import evm2003.utils.equiv
    >>> from gnosis.xml.objectify import make_instance
    >>> a = make_instance('scanned.xml')
    >>> b = make_instance('stored.xml')
    >>> a == b
    1

At the command-line:

    % python equiv.py scanned.xml stored.xml

(lack of any output means success, in that ultra-terse Unix-philosophy
way).

We implement custom .__eq__() and .__ne__() methods specific to cast
ballots.  Injecting such methods is the recommended technique for enhancing
gnosis.xml.objectify objects.

The files scanned.xml and stored.xml documents were used to test this.
They differ in several non-significant respects:
    (1) the top-level attributes occur in a different order;
    (2) non-ordered multi-select contests have selections in a different
        order;
    (3) Write-in votes have different PCDATA content (i.e. nothing for
        scanned.xml).
"""
import gnosis.xml.objectify
import sys

class cast_ballot(gnosis.xml.objectify._XO_):
    def __eq__(self, other):
        metadata = '''election_date country state county
                      number precinct serial'''.split()
        for attr in metadata:
            if getattr(self, attr) != getattr(other, attr):
                return 0
        by_name = lambda a, b: cmp(a.name, b.name)
        self.contest.sort(by_name)
        other.contest.sort(by_name)
        for my, your in zip(self.contest, other.contest):
            if my.name != your.name or \
               my.ordered != your.ordered or \
               my.coupled != your.coupled:
                return 0
            if my.ordered == "No":
                # Compare non-writeins (but don't know if same num writeins)
                my_select = dict([(x.PCDATA,None) for x in my.selection
                                                  if x.writein=="No"])
                your_select = dict([(x.PCDATA,None) for x in your.selection
                                                    if x.writein=="No"])
                if my_select != your_select:
                    return 0
                continue
            for my_select, your_select in zip(my.selection, your.selection):
                if (my_select.writein, your_select.writein) == ("Yes","Yes"):
                    pass
                elif my_select.PCDATA != your_select.PCDATA:
                    return 0
        return 1
    def __ne__(self, other):
        return not self == other

gnosis.xml.objectify._XO_cast_ballot = cast_ballot

if __name__=='__main__':
    a, b = map(gnosis.xml.objectify.make_instance, sys.argv[1:3])
    if a != b:
        print sys.argv[1], "and", sys.argv[2], "are NOT equivalent ballots!"

