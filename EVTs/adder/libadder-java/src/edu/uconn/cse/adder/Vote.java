package edu.uconn.cse.adder;

import java.util.ArrayList;
import java.util.List;
import java.util.StringTokenizer;

public class Vote {
    private List/*<ElgamalCiphertext>*/ cipherList;

    public Vote() {

    }

    public Vote(List/*<ElgamalCiphertext>*/ cipherList) {
        this.cipherList = cipherList;
    }

    public List getCipherList() {
        return cipherList;
    }

    Vote multiply(Vote vote) {
        List/*<ElgamalCiphertext>*/ vec
            = new ArrayList/*<ElgamalCiphertext>*/(this.getCipherList().size());

        for (int i = 0; i < this.getCipherList().size(); i++) {
            ElgamalCiphertext ciphertext1
                = (ElgamalCiphertext) this.getCipherList().get(i);
            ElgamalCiphertext ciphertext2
                = (ElgamalCiphertext) vote.getCipherList().get(i);
            vec.add(ciphertext1.multiply(ciphertext2));
        }

        return new Vote(vec);
    }

    public String shortHash() {
        return "added"; // FIXME
    }

    public static Vote fromString(String s) {
        StringTokenizer st = new StringTokenizer(s, " ");
        List/*<ElgamalCiphertext>*/ cList
            = new ArrayList/*<ElgamalCiphertext>*/(25); // XXX: what size?

        while (st.hasMoreTokens()) {
            String s2 = st.nextToken();

            try {
                ElgamalCiphertext ciphertext = ElgamalCiphertext.fromString(s2);
                cList.add(ciphertext);
            } catch (InvalidElgamalCiphertextException iece) {
                throw new InvalidVoteException(iece.getMessage());
            }
        }

        Vote vote = new Vote(cList);

        return vote;
    }

    public String toString() {
        StringBuffer sb = new StringBuffer(4096);

        for (int i = 0; i < cipherList.size(); i++) {
            ElgamalCiphertext ciphertext
                = (ElgamalCiphertext) cipherList.get(i);
            sb.append(ciphertext.toString());
            sb.append(" ");
        }

        return sb.toString().trim();
    }
}
