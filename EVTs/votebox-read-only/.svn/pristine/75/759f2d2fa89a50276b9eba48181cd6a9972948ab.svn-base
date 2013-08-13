package edu.uconn.cse.adder;

import java.util.NoSuchElementException;
import java.util.StringTokenizer;

import sexpression.ASExpression;
import sexpression.ListExpression;
import sexpression.StringExpression;


/**
 * Represents a vote, and optionally, the corresponding proof.
 *
 * @author David Walluck
 * @version $LastChangedRevision$ $LastChangedDate$
 * @since 0.0.1
 */
public class ElgamalCiphertext {
    private AdderInteger g;
    private AdderInteger h;
    private AdderInteger r;
    private AdderInteger p;
    private MembershipProof proof;

    // XXX: why does p come last here?
    /**
     * Creates a new ElgamalCiphertext with the specified parameter values.
     *
     * @param p the prime
     * @param g the generator
     * @param h the public value
     */
    public ElgamalCiphertext(AdderInteger g, AdderInteger h, AdderInteger p) {
        this.p = p;
        this.g = new AdderInteger(g, p);
        this.h = new AdderInteger(h, p);
        this.r = AdderInteger.ZERO;
    }

    // XXX: now why is r here in that position?
    /**
     * Creates a new ElgamalCiphertext with the specified parameter values.
     *
     * @param p the prime
     * @param g the generator
     * @param h the public value
     * @param r the private random value
     */
    public ElgamalCiphertext(AdderInteger g, AdderInteger h, AdderInteger r,
                AdderInteger p) {
        this.p = p;
        this.g = new AdderInteger(g, p);
        this.h = new AdderInteger(h, p);
        this.r = r;
    }

    /**
     * Returns the short hash of this vote, ignoring the ballot proof.
     *
     * @return the short hash
     */
    public String shortHash() {
        String str = toString();
        int idx = str.indexOf(" ");

        if (idx != -1) {
            str = str.substring(0, idx);
        }

        return Util.sha1(str).substring(0, 5);
    }

    ElgamalCiphertext multiply(ElgamalCiphertext ciphertext) {
        AdderInteger p = this.getP();
        AdderInteger g = this.getG().multiply(ciphertext.getG());
        AdderInteger h = this.getH().multiply(ciphertext.getH());
        AdderInteger r = this.getR().add(ciphertext.getR());

        ElgamalCiphertext newCiphertext = new ElgamalCiphertext(g, h, r, p);

        return newCiphertext;
    }

    /**
     * Returns the prime <tt>p</tt>.
     *
     * @return the prime <tt>p</tt>
     */
    public AdderInteger getP() {
        return p;
    }

    /**
     * Returns the generator <tt>g</tt>.
     *
     * @return the generator <tt>g</tt>
     */
    public AdderInteger getG() {
        return g;
    }

    /**
     * Returns the public value <tt>h</tt>.
     *
     * @return the public value <tt>h</tt>
     */
    public AdderInteger getH() {
        return h;
    }

    /**
     * Returns the private random value <tt>r</tt>.
     *
     * @return the private random value <tt>r</tt>
     */
    public AdderInteger getR() {
        return r;
    }

    /**
     * Returns the proof associated with this vote.
     *
     * @return the proof
     */
    public MembershipProof getProof() {
        return proof;
    }

    /**
     * Sets the proof to the given proof.
     *
     * @param proof the proof
     */
    public void setProof(MembershipProof proof) {
        this.proof = proof;
    }

    /**
     * Creates a <tt>ElgamalCiphertext</tt> from the string standard representation as
     * described in the {@link #toString} method.
     *
     * @param  s a string that specifies a <tt>ElgamalCiphertext</tt>
     * @return a <tt>ElgamalCiphertext</tt> with the specified values
     */
    public static ElgamalCiphertext fromString(String s) {
        StringTokenizer st0 = new StringTokenizer(s, " ");

        try {
            StringTokenizer st = new StringTokenizer(st0.nextToken(), "pGH",
                                                     true);

            if (!st.nextToken().equals("p")) {
                throw new InvalidElgamalCiphertextException("expected token: `p\'");
            }

            AdderInteger p = new AdderInteger(st.nextToken());

            if (!st.nextToken().equals("G")) {
                throw new InvalidElgamalCiphertextException("expected token: `G\'");
            }

            AdderInteger g = new AdderInteger(st.nextToken(), p);

            if (!st.nextToken().equals("H")) {
                throw new InvalidElgamalCiphertextException("expected token: `H\'");
            }

            AdderInteger h = new AdderInteger(st.nextToken(), p);

            if (st.hasMoreTokens()) {
                throw new InvalidElgamalCiphertextException("too many tokens");
            }

            ElgamalCiphertext vote = new ElgamalCiphertext(g, h, p);

            if (st0.hasMoreTokens()) {
                try {
                    vote.setProof(MembershipProof.fromString(st0.nextToken()));
                } catch (InvalidMembershipProofException ibpe) {
                    throw new InvalidElgamalCiphertextException(ibpe.getMessage());
                }
            }

            if (st0.hasMoreTokens()) {
                throw new InvalidElgamalCiphertextException("too many tokens");
            }

            return vote;
        } catch (NoSuchElementException nsee) {
            throw new InvalidElgamalCiphertextException(nsee.getMessage());
        } catch (NumberFormatException nfe) {
            throw new InvalidElgamalCiphertextException(nfe.getMessage());
        }
    }

    /**
     * Returns a <code>String</code> object representing this
     * <code>ElgamalCiphertext</code>.
     * @return the string representation of this vote
     */
    public String toString() {
        StringBuffer sb = new StringBuffer(4096);

        sb.append("p");
        sb.append(p);
        sb.append("G");
        sb.append(g);
        sb.append("H");
        sb.append(h);

        if (proof != null) {
            sb.append(" ");
            sb.append(proof.toString());
        }

        return sb.toString();
    }
    
    /**
     * Method for interop with VoteBox's S-Expression system.
     * 
     * @return the S-Expression equivalent of this AdderInteger
     */
    public ASExpression toASE(){
    	if(proof == null)
    	return new ListExpression(StringExpression.makeString("elgamal-ciphertext"), 
    			p.toASE(), 
    			g.toASE(),
    			h.toASE());
    	
    	return new ListExpression(StringExpression.makeString("elgamal-ciphertext"), 
    			p.toASE(), 
    			g.toASE(),
    			h.toASE(),
    			proof.toASE());
    }
    
    /**
     * Method for interop with VoteBox's S-Expression system.
     * 
     * @param ase - S-Expression representation of an ElgamalCiphertext
     * @return the ElgamalCiphertext equivalent of ase
     */
    public static ElgamalCiphertext fromASE(ASExpression ase){
    	ListExpression list = (ListExpression)ase;
    	
    	if(list.size() != 4 && list.size() != 5)
    		throw new RuntimeException("Not an elgamal-ciphertext");
    	
    	if(!list.get(0).toString().equals("elgamal-ciphertext"))
    		throw new RuntimeException("Not an elgamal-ciphertext");
    	
    	AdderInteger p = AdderInteger.fromASE(list.get(1));
    	AdderInteger g = AdderInteger.fromASE(list.get(2));
    	AdderInteger h = AdderInteger.fromASE(list.get(3));
    	MembershipProof proof = null;
    	
    	if(list.size() == 5)
    		proof = MembershipProof.fromASE(list.get(4));
    	
    	ElgamalCiphertext text = new ElgamalCiphertext(g,h,p);
    	
    	if(proof != null)
    		text.setProof(proof);
    	
    	return text;
    }
}
