package edu.uconn.cse.adder;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.NoSuchElementException;
import java.util.StringTokenizer;

import sexpression.ASExpression;
import sexpression.ListExpression;
import sexpression.StringExpression;

/**
 * Represents a public key.
 *
 * @author David Walluck
 * @version $LastChangedRevision$ $LastChangedDate$
 * @since 0.0.1
 */
public class PublicKey {
    private AdderInteger p;
    private AdderInteger q;
    private AdderInteger g;
    private AdderInteger h;
    private AdderInteger f;

    /**
     * Creates a new PublicKey with the specified parameter values.
     *
     * @param p the prime
     * @param g the generator
     * @param f the message base
     */
    public PublicKey(AdderInteger p, AdderInteger g, AdderInteger f) {
        this.p = p;
        this.q = p.subtract(AdderInteger.ONE).divide(AdderInteger.TWO);
        this.g = g;
        this.f = f;
    }

    /**
     * Creates a new PublicKey with the specified parameter values.
     *
     * @param p the prime
     * @param g the generator
     * @param h the public value
     * @param f the message base
     */
    public PublicKey(AdderInteger p, AdderInteger g, AdderInteger h,
                     AdderInteger f) {
        this.p = p;
        this.q = p.subtract(AdderInteger.ONE).divide(AdderInteger.TWO);
        this.g = g;
        this.h = h;
        this.f = f;
    }

    /**
     * Creates a new PublicKey with the specified parameter values.
     *
     * @param p the prime
     * @param q the sub-prime
     * @param g the generator
     * @param h the public value
     * @param f the message base
     */
    private PublicKey(AdderInteger p, AdderInteger q, AdderInteger g,
                      AdderInteger h, AdderInteger f) {
        this.p = p;
        this.q = q;
        this.g = g;
        this.h = h;
        this.f = f;
    }

    /**
     * Creates a partial public key given the specified prime.
     *
     * @param p the prime
     * @return the public key
     */
   public static PublicKey makePartialKey(AdderInteger p) {
        AdderInteger t;
        AdderInteger a;

        do {
            t = AdderInteger.random(p);
        } while (t.compareTo(AdderInteger.ONE) <= 0);

        AdderInteger g = t.pow(AdderInteger.TWO);

        AdderInteger q = p.subtract(AdderInteger.ONE).divide(AdderInteger.TWO);

        do {
            a = AdderInteger.random(q);
        } while (a.compareTo(AdderInteger.ONE) <= 0);

        AdderInteger f = g.pow(a);

        return new PublicKey(p, q, g, null, f);
    }

    /**
     * Creates a partial public key with the given length in bits.
     *
     * @param length the length of the key to generate in bits
     * @return the public key
     */
    public static PublicKey makePartialKey(int length) {
        return makePartialKey(AdderInteger.safePrime(length));
    }

    /**
     * Creates the corresponding private key of this public key.
     *
     * @return the private key
     */
    public PrivateKey genKeyPair() {
        AdderInteger x = AdderInteger.random(q);

        this.h = g.pow(x);

        return new PrivateKey(p, g, x, f);
    }

    /**
     * Encrypts the given choice given the base.
     * @param choice the choice
     * @param base the base
     *
     * @return the encrypted vote
     */
    private ElgamalCiphertext encrypt(AdderInteger m) {
        AdderInteger r = AdderInteger.random(q);
        AdderInteger bigG = g.pow(r);
        AdderInteger bigH = h.pow(r).multiply(f.pow(m));

        ElgamalCiphertext ciphertext = new ElgamalCiphertext(bigG, bigH, r, p);

        return ciphertext;
    }

    /**
     * Encrypts the given choice given the base.
     *
     * @param choices the choices
     *
     * @return the encrypted vote
     */
    public Vote encrypt(List<AdderInteger> choices) {
        List<ElgamalCiphertext> voteList
            = new ArrayList<ElgamalCiphertext>(choices.size());

        Iterator it;

        for (it = choices.iterator(); it.hasNext();) {
            AdderInteger choice = (AdderInteger) it.next();
            voteList.add(encrypt(choice));
        }

        Vote vote = new Vote(voteList);

        return vote;
    }

    /**
     * Encrypts a polynomial of the given value.
     * @param m the message
     *
     * @return the encrypted vote
     */
    public ElgamalCiphertext encryptPoly(AdderInteger m) {
        AdderInteger r = AdderInteger.random(q);
        AdderInteger bigG = g.pow(r);
        AdderInteger mPlusOne = new AdderInteger(m.add(AdderInteger.ONE), p);
        AdderInteger bigH = h.pow(r).multiply(mPlusOne.pow(AdderInteger.TWO));

        //XXX:  This is a VoteBox related change.  We need to keep r around, but not send it over the wire
        ElgamalCiphertext ciphertext = new ElgamalCiphertext(bigG, bigH, r, p);

        return ciphertext;
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
     * Returns the sub-prime <tt>q</tt>.
     *
     * @return the sub-prime <tt>q</tt>
     */
    public AdderInteger getQ() {
        return q;
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
     * Returns the message base <tt>f</tt>.
     *
     * @return the message base <tt>f</tt>
     */
    public AdderInteger getF() {
        return f;
    }

    /**
     * Creates a <tt>PublicKey</tt> from the string standard representation as
     * described in the {@link #toString} method.
     *
     * @param  s a string that specifies a <tt>PublicKey</tt>
     * @return a <tt>PublicKey</tt> with the specified values
     */
    public static PublicKey fromString(String s) {
        StringTokenizer st = new StringTokenizer(s, "pghf", true);

        try {
            if (!st.nextToken().equals("p")) {
                throw new InvalidPublicKeyException("expected token: `p\'");
            }

            AdderInteger p = new AdderInteger(st.nextToken());
            AdderInteger q = p.subtract(AdderInteger.ONE)
                              .divide(AdderInteger.TWO);

            if (!st.nextToken().equals("g")) {
                throw new InvalidPublicKeyException("expected token: `g\'");
            }

            AdderInteger g = new AdderInteger(st.nextToken(), p);

            if (!st.nextToken().equals("h")) {
                throw new InvalidPublicKeyException("expected token: `h\'");
            }

            AdderInteger h = new AdderInteger(st.nextToken(), p);

            if (!st.nextToken().equals("f")) {
                throw new InvalidPublicKeyException("expected token: `f\'");
            }

            AdderInteger f = new AdderInteger(st.nextToken(), p);

            if (st.hasMoreTokens()) {
                throw new InvalidPublicKeyException("too many tokens");
            }

            return new PublicKey(p, q, g, h, f);
        } catch (NoSuchElementException nsee) {
            throw new InvalidPublicKeyException(nsee.getMessage());
        } catch (NumberFormatException nfe) {
            throw new InvalidPublicKeyException(nfe.getMessage());
        }
    }

    /**
     * Returns a <code>String</code> object representing this
     * <code>PublicKey</code>.
     * @return the string representation of this public key
     */
    public String toString() {
        StringBuffer sb = new StringBuffer(4096);

        sb.append("p");
        sb.append(p.toString());
        sb.append("g");
        sb.append(g.toString());
        sb.append("h");

        if (h != null) {
            sb.append(h.toString());
        } else {
            sb.append("0");
        }

        sb.append("f");
        sb.append(f.toString());

        return sb.toString();
    }
    
    /**
     * Method for interop with VoteBox's S-Expression system.
     * 
     * @return the S-Expression equivalent of this PublicKey
     */
    public ASExpression toASE(){
    	AdderInteger ourH = h;
    	
    	if(ourH == null) ourH = AdderInteger.ZERO;
    	
    	return new ListExpression(
    			StringExpression.makeString("public-key"),
    			p.toASE(),
    			g.toASE(),
    			ourH.toASE(),
    			f.toASE());
    }
    
    /**
     * Method for interop with VoteBox's S-Expression system.
     * 
     * @param ase - S-Expression representation of a PublicKey
     * @return the PublicKey equivalent of ase
     */
    public static PublicKey fromASE(ASExpression ase){
    	ListExpression exp = (ListExpression)ase;
    	if(!(exp.get(0).toString()).equals("public-key"))
    		throw new RuntimeException("Not public-key");
    	
    	AdderInteger p = AdderInteger.fromASE(exp.get(1));
    	AdderInteger g = AdderInteger.fromASE(exp.get(2));
    	AdderInteger h = AdderInteger.fromASE(exp.get(3));
    	AdderInteger f = AdderInteger.fromASE(exp.get(4));
    	
    	AdderInteger q = p.subtract(AdderInteger.ONE).divide(AdderInteger.TWO);
    	
    	return new PublicKey(p, q, g, h, f);
    }
    
    /**
     * We need to test for equality between two keys in some places, just for sanities sake.
     * 
     * @param o - object to test against
     */
    @Override
    public boolean equals(Object o){
    	if(!(o instanceof PublicKey))
    		return false;
    	
    	return o.toString().equals(toString());
    }
}
