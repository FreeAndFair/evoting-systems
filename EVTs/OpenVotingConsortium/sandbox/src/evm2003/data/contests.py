"""This data should come from ballot-election.xml

- But for now include a fallback definition if the XML is unavailable
- Also, send the Python code to STDOUT if run as main (semi-Quine)
"""
from os.path import isfile
xml_data = 'ballot-election.xml'

if isfile(xml_data):
    from gnosis.xml.objectify import make_instance
    ballot = make_instance('ballot-election.xml')
    contnames, cont = [], {}
    for contest in ballot.contest:
        name = contest.name
        contnames.append(name)
        if contest.coupled=="No":
            cont[name] = [select.PCDATA for select in contest.selection]
            if contest.allow_writein=="Yes":
                cont[name].append("")
        else:
            cont[name] = []
            for n in range(0, len(contest.selection), 2):
                cont[name].append([s.PCDATA for s in contest.selection[n:n+2]])
            if contest.allow_writein=="Yes":
                cont[name].append(["",""])
else:
    contnames = ["Presidency", "Senator", "U.S. Representative", "Treasurer",
                 "Attorney General", "Commis. of Education", "State Senate",
                 "State Assembly", "Transportation Initiative",
                 "Health care initiative", "Term limits", "Cat Catcher",
                 "County Commissioner"]
    cont = {
        "Presidency": [
            ["George Washington", "Abraham Lincoln"],
            ["Thomas Jefferson", "Harry S. Truman"],
            ["Rachel Carson", "John Muir"],
            ["Susan B. Anthony", "Betsy Ross"],
            ["V. I. Lenin", "Karl Marx"],
            ["Martin Luther King", "John Anderson"],
            ["Helen Keller", "Amelia Earhart"],
            ["", ""]],
        "Senator": [
            "Frances E. Willard",
            "Lucy Stone",
            "Karl Menninger",
            "Jane Addams",
            "Clarence Darrow",
            "William Lloyd Garrison",
            "Sidney Hillman",
            ""],
        "U.S. Representative": [
            "Ignace Paderewski",
            "Lillian Hellman",
            ""],
        "Treasurer": [
            "Tom Cosgrove",
            "John Gallagher",
            ""],
        "Attorney General": [
            "Dewitt Clinton",
            "Charles Parnell",
            "Thomas P. O'Neill Jr",
            ""],
        "Commis. of Education": [
            "Christian Doppler",
            "Carl Sagan",
            ""],
        "State Senate": [
            "Robert Ingersoll",
            "Martin Luther",
            "Barbara Jordon",
            ""],
        "State Assembly": [
            "Don Lee",
            "Langston Hughes",
            ""],
        "Transportation Initiative": [
            "Yes",
            "No"],
        "Health care initiative": [
            "Yes",
            "No"],
        "Term limits": [
            "Yes",
            "No"],
        "Cat Catcher": [
            "Regis Philbin",
            "Oprah Winfrey",
            "Howard Stern",
            "Charlie Rose",
            "Rosie O'Donnell",
            "Carrie Fisher",
            "Steven Spielberg",
            "Queen Latifah",
            "Eddie Murphy",
            ""],
        "County Commissioner": [
            "David Packard",
            "William Hewlett",
            "Steve Jobs",
            "Steve Wozniak",
            "William Shockely",
            "Gordon Moore",
            "Philip Kahn",
            ""]}

if __name__=='__main__':
    from pprint import pprint
    print "contnames = \\"
    pprint(contnames)
    print "cont = \\"
    pprint(cont)
