import sys
if sys.platform != 'win32':
    sys.path.append('../..')
else:
    sys.path.append('..\\..')
from evm2003.data.contests import cont

length = [8, 8, 3, 3, 4, 3, 4, 3, 2, 2, 2, 10, 8]
writein = [1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1]

def ballotxml(date, country, State, county, ballot_number, precinct, serial, source, sel, writeins):
    xml = ""
    xml += '<cast_ballot election_date="' + str(date)[0:4] + "-" + str(date)[4:6] + "-" + str(date)[6:8] + '" country="' + country + '" state="' + State + '" county="' + county + '" number="' + str(ballot_number) + '" precinct="' + str(precinct) + '" serial="' + str(serial) + '" source="' + source + '">\n'
    n = 0
    for name in ["Presidency", "Senator", "U.S. Representative", "Treasurer", "Attorney General", "Commis. of Education", "State Senate", "State Assembly", "Transportation Initiative", "Health care initiative", "Term limits", "Cat Catcher", "County Commissioner"]:
        coupled="No"
        if n == 0: coupled = "Yes"
        ordered = "No"
        if n == 12: ordered = "Yes"
        xml += '  <contest ordered="' + ordered + '" coupled="' + coupled + '" name="' + name + '">\n'
        if n == 0:
            if sel[n] == 0:
                xml += '    <selection writein="No" name="President">No preference indicated</selection>\n'
                xml += '    <selection writein="No" name="Vice President">No preference indicated</selection>\n'
            elif sel[n] < length[n]:
                xml += '    <selection writein="No" name="President">' + cont[name][sel[n]-1][0] + '</selection>\n'
                xml += '    <selection writein="No" name="Vice President">' + cont[name][sel[n]-1][1] + '</selection>\n'
            else:
                xml += '    <selection writein="Yes" name="President">' + writeins[n][0] + '</selection>\n'
                xml += '    <selection writein="Yes" name="Vice President">' + writeins[n][1] + '</selection>\n'
        elif n < 11:
            if sel[n] == 0:
                xml += '    <selection writein="No">No preference indicated</selection>\n'
            elif sel[n] < length[n] or writein[n] == 0:
                xml += '    <selection writein="No">' + cont[name][sel[n]-1] + '</selection>\n'
            else:
                xml += '    <selection writein="Yes">' + writeins[n] + '</selection>\n'
        elif sel[n] == []:
            xml += '    <selection writein="No">No preference indicated</selection>\n'
        else:
            for i in sel[n]:
                if i < length[n]:
                    choice = cont[name][i-1]
                    wri = "No"
                else:
                    choice = writeins[n]
                    wri = "Yes"
                xml += '    <selection writein="' + wri + '">' + choice + '</selection>\n'
                wri = "Yes"
        xml += '  </contest>\n'
        n += 1
    xml += '</cast_ballot>\n'
    return xml