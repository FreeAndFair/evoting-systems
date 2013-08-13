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
 * Represents a private key.
 *
 * @author David Walluck
 * @version $LastChangedRevision$ $LastChangedDate$
 * @since 0.0.1
 */
public class PrivateKey {
    private AdderInteger p;
    private AdderInteger q;
    private AdderInteger g;
    private AdderInteger x;
    private AdderInteger f;

    /**
     * Creates a new PrivateKey with the specified parameter values.
     *
     * @param p the prime
     * @param g the generator
     * @param x the private value
     * @param f the message base
     */
    public PrivateKey(AdderInteger p, AdderInteger g, AdderInteger x,
                      AdderInteger f) {
        this.p = p;
        this.q = p.subtract(AdderInteger.ONE).divide(AdderInteger.TWO);
        this.g = g;
        this.x = x;
        this.f = f;
    }

    /**
     * Returns the partial decrytion of the given vote.
     * @param vote the vote
     *
     * @return the partial decryption of the given vote
     */
    public List<AdderInteger> partialDecrypt(Vote vote) {
        List<ElgamalCiphertext> cipherList = vote.getCipherList();
        List<AdderInteger> resultList = new ArrayList<AdderInteger>(cipherList.size());

        for (Iterator it = cipherList.iterator(); it.hasNext();) {
            AdderInteger bigG = ((ElgamalCiphertext) it.next()).getG();
            resultList.add(bigG.pow(x));
        }

        return resultList;
    }

    /**
     * Returns the final private key given a list of polynomials.
     * @param polyList the polynomial list
     *
     * @return the final private key
     */
    public PrivateKey getFinalPrivKey(List/*<ElgamalCiphertext>*/ polyList) {
        AdderInteger total = new AdderInteger(AdderInteger.ZERO, q);

        /*for (ElgamalCiphertext ciphertext : polyList) {*/
        for (Iterator it = polyList.iterator(); it.hasNext();) {
            ElgamalCiphertext ciphertext = (ElgamalCiphertext) it.next();
            AdderInteger eL = ciphertext.getG();
            AdderInteger eR = ciphertext.getH();
            AdderInteger product = eL.pow(x.negate()).multiply(eR);
            AdderInteger qPlusOneOverTwo = q.add(AdderInteger.ONE)
                                            .divide(AdderInteger.TWO);
            AdderInteger posInverse = product.pow(qPlusOneOverTwo);
            AdderInteger negInverse = posInverse.negate();
            AdderInteger inverse;

            if (posInverse.compareTo(negInverse) < 0) {
                inverse = posInverse;
            } else {
                inverse = negInverse;
            }

            inverse = inverse.subtract(AdderInteger.ONE);

            total = total.add(inverse);
        }

        return new PrivateKey(p, g, total, f);
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
     * @return the sub-prime <tt>q</tt>.
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
     * Returns the private value <tt>x</tt>.
     *
     * @return the private value <tt>x</tt>
     */
    public AdderInteger getX() {
        return x;
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
     * Creates a <tt>PrivateKey</tt> from the string standard representation as
     * described in the {@link #toString} method.
     *
     * @param  s a string that specifies a <tt>PrivateKey</tt>
     * @return a <tt>PrivateKey</tt> with the specified values
     */
    public static PrivateKey fromString(String s) {
        StringTokenizer st = new StringTokenizer(s, "pgxf", true);

        try {
            if (!st.nextToken().equals("p")) {
                throw new InvalidPrivateKeyException("expected token: `p\'");
            }

            AdderInteger p = new AdderInteger(st.nextToken());

            if (!st.nextToken().equals("g")) {
                throw new InvalidPrivateKeyException("expected token: `g\'");
            }

            AdderInteger g = new AdderInteger(st.nextToken(), p);

            if (!st.nextToken().equals("x")) {
                throw new InvalidPrivateKeyException("expected token: `x\'");
            }

            AdderInteger x = new AdderInteger(st.nextToken(),
                                              p.subtract(AdderInteger.ONE)
                                              .divide(AdderInteger.TWO));

            if (!st.nextToken().equals("f")) {
                throw new InvalidPrivateKeyException("expected token: `f\'");
            }

            AdderInteger f = new AdderInteger(st.nextToken(), p);

            if (st.hasMoreTokens()) {
                throw new InvalidPrivateKeyException("too many tokens");
            }

            return new PrivateKey(p, g, x, f);
        } catch (NoSuchElementException nsee) {
            throw new InvalidPrivateKeyException(nsee.getMessage());
        } catch (NumberFormatException nfe) {
            throw new InvalidPrivateKeyException(nfe.getMessage());
        }
    }

    /**
     * Returns a <code>String</code> object representing this
     * <code>PrivateKey</code>.
     * @return the string representation of this private key
     */
    public String toString() {
        StringBuffer sb = new StringBuffer(4096);

        sb.append("p");
        sb.append(p.toString());
        sb.append("g");
        sb.append(g.toString());
        sb.append("x");
        sb.append(x.toString());
        sb.append("f");
        sb.append(f.toString());

        return sb.toString();
    }
    
    /**
     * Method for interop with VoteBox's S-Expression system.
     * 
     * @return the S-Expression equivalent of this PrivateKey
     */
    public ASExpression toASE(){
    	return new ListExpression(
    		StringExpression.makeString("private-key"),
    		p.toASE(),
    		g.toASE(),
    		x.toASE(),
    		f.toASE()
    	);
    }
    
    /**
     * Method for interop with VoteBox's S-Expression system.
     * 
     * @param ase - S-Expression representation of a PrivateKey
     * @return the PrivateKey equivalent of ase
     */
    public static PrivateKey fromASE(ASExpression ase){
    	ListExpression exp = (ListExpression)ase;
    	
    	if(!(exp.get(0).toString()).equals("private-key"))
    		throw new RuntimeException("Not private-key");
    	
    	AdderInteger p = AdderInteger.fromASE(exp.get(1));
    	AdderInteger g = AdderInteger.fromASE(exp.get(1));
    	AdderInteger x = AdderInteger.fromASE(exp.get(1));
    	AdderInteger f = AdderInteger.fromASE(exp.get(1));
    	
    	return new PrivateKey(p, g, x, f);
    }
}
