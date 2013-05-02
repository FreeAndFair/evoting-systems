package edu.uconn.cse.adder;

import java.util.ArrayList;
import java.util.List;
import java.util.StringTokenizer;

public class VoteProof {
    private AdderInteger p;
    private List/*<MembershipProof>*/ proofList;
    private MembershipProof sumProof;

    public VoteProof() {

    }

    private VoteProof(MembershipProof sumProof,
                      List/*<MembershipProof>*/ proofList) {
        this.sumProof = sumProof;
        this.proofList = proofList;
    }

    public void compute(Vote vote, PublicKey pubKey,
                        List/*<AdderInteger>*/ choices, int min, int max) {
        this.p = pubKey.getP();
        List/*<ElgamalCiphertext>*/ cipherList = vote.getCipherList();
        List/*<AdderInteger>*/ cipherDomain
            = new ArrayList/*<AdderInteger>*/(2);

        cipherDomain.add(AdderInteger.ZERO);
        cipherDomain.add(AdderInteger.ONE);

        ElgamalCiphertext sumCipher
            = new ElgamalCiphertext(AdderInteger.ONE, AdderInteger.ONE, p);

        int numChoices = 0;
        int size = cipherList.size();
        this.proofList = new ArrayList(size);

        for (int i = 0; i < size; i++) {
            MembershipProof proof = new MembershipProof();
            ElgamalCiphertext ciphertext
                = (ElgamalCiphertext) cipherList.get(i);
            AdderInteger choice = (AdderInteger) choices.get(i);
            proof.compute(ciphertext, pubKey, choice, cipherDomain);
            this.proofList.add(proof);

            sumCipher = sumCipher.multiply(ciphertext);

            if (choice.equals(AdderInteger.ONE)) {
                numChoices++;
            }
        }

        List/*<AdderInteger>*/ totalDomain
            = new ArrayList/*<AdderInteger>*/(max + 1);

        for (int j = min; j <= max; j++) {
            totalDomain.add(new AdderInteger(j));
        }

        this.sumProof = new MembershipProof();
        this.sumProof.compute(sumCipher, pubKey, new AdderInteger(numChoices), totalDomain);
    }


    public boolean verify(Vote vote, PublicKey pubKey, int min, int max) {
        this.p = pubKey.getP();
        List/*<ElgamalCiphertext>*/ cipherList = vote.getCipherList();
        List/*<AdderInteger>*/ cipherDomain
            = new ArrayList/*<AdderInteger>*/(2);

        cipherDomain.add(AdderInteger.ZERO);
        cipherDomain.add(AdderInteger.ONE);

        ElgamalCiphertext sumCipher
            = new ElgamalCiphertext(AdderInteger.ONE, AdderInteger.ONE, p);
        int size = this.proofList.size();

        for (int i = 0; i < size; i++) {
            MembershipProof proof = (MembershipProof) this.proofList.get(i);
            ElgamalCiphertext ciphertext
                = (ElgamalCiphertext) cipherList.get(i);

            if (!proof.verify(ciphertext, pubKey, cipherDomain)) {
                return false;
            }

            sumCipher = sumCipher.multiply(ciphertext);
        }

        List/*<AdderInteger>*/ totalDomain
            = new ArrayList/*<AdderInteger>*/(max + 1);

        for (int j = min; j <= max; j++) {
            totalDomain.add(new AdderInteger(j));
        }

        if (!this.sumProof.verify(sumCipher, pubKey, totalDomain)) {
            return false;
        }

        return true;
    }

    public static VoteProof fromString(String s) {
        StringTokenizer st = new StringTokenizer(s, " ");
        List/*<ElgamalCiphertext>*/ pList
            = new ArrayList/*<ElgamalCiphertext>*/(25); // XXX: what size? 
        MembershipProof sumProof = MembershipProof.fromString(st.nextToken());

        while (st.hasMoreTokens()) {
            String s2 = st.nextToken();
            MembershipProof proof = MembershipProof.fromString(s2);
            pList.add(proof);
        }

        VoteProof voteProof = new VoteProof(sumProof, pList);

        return voteProof;
    }

    public String toString() {
        StringBuffer sb = new StringBuffer(4096);

        sb.append(sumProof.toString());

        for (int i = 0; i < proofList.size(); i++) {
            MembershipProof proof = (MembershipProof) proofList.get(i);
            sb.append(" ");
            sb.append(proof.toString());
        }

        return sb.toString();
    }
}
