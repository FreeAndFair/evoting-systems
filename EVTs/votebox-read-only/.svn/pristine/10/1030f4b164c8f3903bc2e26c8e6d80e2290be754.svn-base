package edu.uconn.cse.adder;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

/**
 * Represents an election.
 *
 * @author David Walluck
 * @version $LastChangedRevision$ $LastChangedDate$
 * @since 0.0.1
 */
public class Election {
    private AdderInteger p;
    private List<Vote> votes;

    /**
     * Creates a new election.
     *
     * @param p the prime
     */
    public Election(AdderInteger p) {
        this.p = p;
        this.votes = new ArrayList<Vote>();
    }

    /**
     * Gets the votes of this election.
     *
     * @return the voes
     */
    public List<Vote> getVotes() {
        return votes;
    }

    /**
     * Casts the given vote in this election.
     *
     * @param vote the vote
     */
    public void castVote(Vote vote) {
        votes.add(vote);
    }

    /**
     * Sums the votes cast in this election.
     * This is the product of the votes modulo <tt>p</tt>).
     *
     * @return a vote representing the total of the given list of votes
     */
    public Vote sumVotes() {
        Vote vote = (Vote) votes.get(0);
        int size = vote.getCipherList().size();
        List<ElgamalCiphertext> initList = new 
            ArrayList<ElgamalCiphertext>(size);

        for (int i = 0; i < size; i++) {
            ElgamalCiphertext ciphertext
                = new ElgamalCiphertext(AdderInteger.ONE, AdderInteger.ONE,
                                        p);
            initList.add(ciphertext);
        }

        Vote total = new Vote(initList);

        /*for (Vote vote : votes) {*/
        for (Iterator it = votes.iterator(); it.hasNext();) {
            Vote vote2 = (Vote) it.next();
            total = vote2.multiply(total);
        }

        return total;
    }

    /**
     * Gets the final sum given the partial sums, the coefficients, the vote
     * representing the sum, and the master public key.
     *
     * @param  partialSums the partial sums
     * @param  coeffs      the coefficients
     * @param  sum         the sum
     * @param  masterKey   the master public key
     * @return the final vote tally
     */
    public List<AdderInteger>
                    getFinalSum(List<List<AdderInteger>> partialSums,
                    List<AdderInteger> coeffs, Vote sum,
                    PublicKey masterKey) {
        AdderInteger p = masterKey.getP();
        AdderInteger q = masterKey.getQ();
        AdderInteger f = masterKey.getF();
        AdderInteger g = masterKey.getG();

        Polynomial poly = new Polynomial(p, g, f, coeffs);
        List<AdderInteger> lagrangeCoeffs = poly.lagrange();
        int lsize = lagrangeCoeffs.size();

        List<ElgamalCiphertext> cipherList = sum.getCipherList();
        int csize = cipherList.size();
        List<AdderInteger> productList
            = new ArrayList<AdderInteger>(csize);
        List<AdderInteger> results
            = new ArrayList<AdderInteger>(csize);

        for (int i = 0; i < csize; i++) {
            productList.add(new AdderInteger(AdderInteger.ONE, p));

            for (int j = 0; j < lsize; j++) {
                AdderInteger pli = (AdderInteger) productList.get(i);
                List ps = (List) partialSums.get(j);
                AdderInteger psi = (AdderInteger) ps.get(i);
                AdderInteger lcj = (AdderInteger) lagrangeCoeffs.get(j);
                AdderInteger product = psi.pow(lcj).multiply(pli);
                productList.set(i, product);
            }

            AdderInteger bigH = ((ElgamalCiphertext) cipherList.get(i)).getH();
            AdderInteger target = bigH.divide((AdderInteger) productList.get(i));
            AdderInteger j = null;
            boolean gotResult = false;

            int numVotes = votes.size();

            //System.out.println("Looping " + (numVotes + 1) + " times to look for result");

            for (int k = 0; k <= numVotes; k++) {
                j = new AdderInteger(k, q);

                //System.out.println("DOES " + new AdderInteger(f, p).pow(j) + " equal " + target + "?");

                if (f.pow(j).equals(target)) {
                    //System.out.println("GOT RESULT!!!");
                    gotResult = true;
                    break;
                }
            }

            if (gotResult) {
                //System.out.println("Adding result: " + j);
                results.add(j);
                gotResult = false;
            } else {
                //System.out.println("THROWING EXCEPTION!!!");
                throw new SearchSpaceExhaustedException("Error searching for "
                                                        + target);
            }
        }

        return results;
    }
}
