# -*- coding: iso-8859-1 -*-
# Various conversion utilities.
#
# Version: 1.1
# Author: Jan Krrman
# Revision: David Mertz

import string
import sys, os
sys.path.append('..%s..' % os.sep)
from evm.data.contests import cont

def obscure(key, num):
    """Obscure a number.

    Parameters:
        key: A decimal string - used for the obscuration.
        num: A decimal string - the number to be obscured.

    Use revert() to get back the original number.
    """
    digits = [(int(k)+int(n)) % 10 for k, n in zip(key*9, num)]
    return "".join(map(str, digits))

def revert(key, num):
    """Revert a number previously obscured by obscure().

    Parameters:
        key: A decimal string - should be the same as used for the obscuration.
        num: A decimal string - the obscured number to be reverted.
    """
    return obscure(key, num)

def todecimal(bin):
    """Convert a binary number to decimal.

    Parameters:
        bin: The binary number as a list of bits
    """
    dec = 0
    pow = 2**(len(bin)-1)
    for i in bin:
        dec += i*pow
        pow /= 2
    return dec

def tobinary(dec):
    """Convert a decimal number to binary.

    Parameters:
        dec: The decimal number
    """
    bin = []
    while dec > 0:
        bit = int(dec % 2)
        bin.insert(0, bit)
        dec = (dec - bit)/2
    return bin

def votes2digits(file):
    """Encode the casted votes as a decimal number.

    Parameters:
        file: An XML file containing the casted votes (vote-selection.xml)
    """
    from gnosis.xml.objectify import make_instance

    bits = []
    ballot = make_instance(file)
    ballotno = ballot.number
    for contest in ballot.contest:
        name = contest.name
        if contest.ordered == "No":
            b = [0] * len(cont[contest.name])
        else:
            b = [0] * len(cont[contest.name])**2
        n = 0
        for selection in contest.selection:
            if contest.name == "Presidency" and selection.name == "Vice President":
                text = [text, selection.PCDATA]
            else:
                text = selection.PCDATA
            if not (contest.name == "Presidency" and selection.name == "President"):
                if text != "No preference indicated" and text != ["No preference indicated", "No preference indicated"]:
                    if selection.writein == "No":
                        ind = cont[contest.name].index(text)
                        if contest.ordered == "No":
                            b[ind] = 1
                        else:
                            b[ind*len(cont[contest.name])+n] = 1
                    elif contest.ordered == "No":
                        b[-1] = 1
                    else:
                        b[-len(cont[contest.name])+n] = 1
            n += 1
        bits += b
    # The string must have exacly 36 digits - insert leading zeroes
    digits = "%036d" % todecimal(bits)
    return ballotno + digits

def digits2votes(digits):
    """Get the casted votes from the decimal bar code number.

    Parameters:
        digits: A decimal number (obscured by obscure()) that encode the votes.

    The returned list of votes has 13 elements, one for each contest.
    The first 11 are numbers, and the last two are lists of numbers, where
    each number gives the selected candidate. A zero, or an empty list for
    the last two contests, indicates a blank vote. If the decimal number does
    not represent a correct vote, an empty list is returned.
    """
    bits = tobinary(long(revert(digits[:4], digits[4:])))
    if len(digits) != 40 or len(bits) > 116:
        print digits, len(digits)
        print bits, len(bits)
        #raise ValueError  # we definitely need some error-checking here
        return []
    for i in range(116-len(bits)):
        bits.insert(0, 0)
    length = [8, 8, 3, 3, 4, 3, 4, 3, 2, 2, 2, 10, 8, 8, 8, 8, 8, 8, 8, 8]
    offset = 0
    cat = []
    rank = [0] * 8
    votes = [0] * 11
    for i in range(len(length)):
        contest = bits[offset:offset+length[i]]
        casted = 0
        for j in range(len(contest)):
            if contest[j] == 1:
                casted += 1
                if i != 11 and casted > 1 or i == 11 and casted > 3:
                    return []
                if i < 11:
                    votes[i] = j+1
                elif i == 11:
                    cat.append(j+1)
                else:
                    if rank[j] == 0:
                        rank[j] = i-11
                    else:
                        return []
        offset += length[i]
    votes.append(cat)
    commiss = []
    flag = 0
    for i in rank:
        if i > 0:
            if flag == 0:
                commiss.append(i)
            else:
                return []
        else:
            flag = 1
    votes.append(commiss)
    return votes
