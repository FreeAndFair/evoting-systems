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
               my.ordered!=your.ordered or \
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
    else:
        print sys.argv[1], "and", sys.argv[2], "are equivalent ballots!"