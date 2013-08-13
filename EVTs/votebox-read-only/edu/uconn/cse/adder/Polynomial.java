package edu.uconn.cse.adder;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.StringTokenizer;
import java.util.NoSuchElementException;

/**
 * Represents a polynomial.
 *
 * @author David Walluck
 * @version $LastChangedRevision$ $LastChangedDate$
 * @since 0.0.1
 */
public class Polynomial {
    private AdderInteger p;
    private AdderInteger q;
    private AdderInteger g;
    private AdderInteger f;
    private int degree;
    private List<AdderInteger> coeffs;

    /**
     * Creates a new Polynomial of degree 0 with the specified parameter
     * values.
     *
     * @param p the prime
     * @param g the generator
     * @param f the message base
     */
    public Polynomial(AdderInteger p, AdderInteger g, AdderInteger f) {
        this.p = p;
        this.q = p.subtract(AdderInteger.ONE).divide(AdderInteger.TWO);
        this.g = g;
        this.f = f;
        this.degree = 0;
    }

    /**
     * Creates a new Polynomial of the given degree with the specified parameter
     * values and random coefficients.
     *
     * @param p the prime
     * @param g the generator
     * @param f the message base
     * @param degree the degree
     */
    public Polynomial(AdderInteger p, AdderInteger g, AdderInteger f,
                     int degree) {
        this.p = p;
        this.q = p.subtract(AdderInteger.ONE).divide(AdderInteger.TWO);
        this.g = g;
        this.f = f;
        this.degree = degree;
        coeffs = new ArrayList<AdderInteger>(degree + 1);

        for (int i = 0; i <= degree; i++) {
            coeffs.add(AdderInteger.random(q));
        }
    }

    /**
     * Creates a new PrivateKey with the specified parameter values and given
     * coefficients.
     *
     * @param p      the prime
     * @param g      the generator
     * @param f      the message base
     * @param coeffs the coefficients
     */
    public Polynomial(AdderInteger p, AdderInteger g, AdderInteger f,
                      List<AdderInteger> coeffs) {
        this.p = p;
        this.q = p.subtract(AdderInteger.ONE).divide(AdderInteger.TWO);
        this.g = g;
        this.f = f;
        this.degree = coeffs.size() - 1;
        this.coeffs = coeffs;
    }

    /**
     * Creates a new PrivateKey with the specified parameter values and given
     * coefficients.
     *
     * @param p      the prime
     * @param q      the sub-prime
     * @param g      the generator
     * @param f      the message base
     * @param coeffs the coefficients
     */
    private Polynomial(AdderInteger p, AdderInteger q, AdderInteger g,
                       AdderInteger f, List<AdderInteger> coeffs) {
        this.p = p;
        this.q = q;
        this.g = g;
        this.f = f;
        this.degree = coeffs.size() - 1;
        this.coeffs = coeffs;
    }

    /**
     * Evaluates the polynomial at the given point <tt>x</tt>.
     *
     * @param  x the point at which to evaluate the polynomial
     * @return the value of the polynomial evaluated at the given point
     */
    public AdderInteger evaluate(AdderInteger x) {
        AdderInteger evalSum = new AdderInteger(AdderInteger.ZERO, q);

        int size = coeffs.size();
        /*for (AdderInteger c : coeffs) {*/
        for (int i = 0; i < size; i++) {
            AdderInteger c = (AdderInteger) coeffs.get(i);
            evalSum = evalSum.add(c.multiply(new AdderInteger(x, q).pow(i)));
        }

        return evalSum;
    }

    /**
     * Returns the Lagrange coefficients of this polynomial.
     *
     * @return the list of Lagrange coefficients of this polynomial
     */
    public List<AdderInteger> lagrange() {
        List<AdderInteger> lagrangeCoeffs =
            new ArrayList<AdderInteger>(coeffs.size());

        /*for (AdderInteger ai : coeffs) {*/
        for (Iterator it = coeffs.iterator(); it.hasNext();) {
            AdderInteger ai = (AdderInteger) it.next();
            AdderInteger numerator = new AdderInteger(AdderInteger.ONE, q);

            /*for (AdderInteger aj : coeffs) {*/
            for (Iterator it2 = coeffs.iterator(); it2.hasNext();) {
                AdderInteger aj = (AdderInteger) it2.next();

                if (!ai.equals(aj)) {
                    numerator = numerator.multiply(q.subtract(aj));
                }
            }

            AdderInteger denominator = new AdderInteger(AdderInteger.ONE, q);

            /*for (AdderInteger aj : coeffs) {*/
            for (Iterator it2 = coeffs.iterator(); it2.hasNext();) {
                AdderInteger aj = (AdderInteger) it2.next();

                if (!ai.equals(aj)) {
                    denominator = denominator.multiply(ai.subtract(aj));
                }
            }

            lagrangeCoeffs.add(numerator.divide(denominator));
        }

        return lagrangeCoeffs;
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
     * Returns the message base <tt>f</tt>.
     *
     * @return the message base <tt>f</tt>
     */
    public AdderInteger getF() {
        return f;
    }

    /**
     * Returns the list of coefficients of this polynomial.
     *
     * @return the list of coefficients
     */
    public List<AdderInteger> getCoeffs() {
        return coeffs;
    }

    /**
     * Returns the degree of this polynomial.
     *
     * @return the degree
     */
    public int getDegree() {
        return degree;
    }

    /**
     * Creates a <tt>Polynomial</tt> from the string standard representation as
     * described in the {@link #toString} method.
     *
     * @param  s a string that specifies a <tt>Polynomial</tt>
     * @return a <tt>Polynomial</tt> with the specified values
     */
    public static Polynomial fromString(String s) {
        StringTokenizer st0 = new StringTokenizer(s, " ");

        try {
            StringTokenizer st = new StringTokenizer(st0.nextToken(), "pgf",
                                                     true);

            if (!st.nextToken().equals("p")) {
                throw new InvalidPolynomialException("expected token: `p\'");
            }

            AdderInteger p = new AdderInteger(st.nextToken());
            AdderInteger q = p.subtract(AdderInteger.ONE)
                              .divide(AdderInteger.TWO);

            if (!st.nextToken().equals("g")) {
                throw new InvalidPolynomialException("expected token: `g\'");
            }

            AdderInteger g = new AdderInteger(st.nextToken(), p);

            if (!st.nextToken().equals("f")) {
                throw new InvalidPolynomialException("expected token: `f\'");
            }

            AdderInteger f = new AdderInteger(st.nextToken(), p);

            if (st.hasMoreTokens()) {
                throw new InvalidPolynomialException("too many tokens");
            }

            List<AdderInteger> coeffs = new ArrayList<AdderInteger>();

            while (st0.hasMoreTokens()) {
                coeffs.add(new AdderInteger(st0.nextToken(), q));
            }

            return new Polynomial(p, q, g, f, coeffs);
        } catch (NoSuchElementException nsee) {
            throw new InvalidPolynomialException(nsee.getMessage());
        } catch (NumberFormatException nfe) {
            throw new InvalidPolynomialException(nfe.getMessage());
        }
    }

    /**
     * Returns a <code>String</code> object representing this
     * <code>Polynomial</code>.
     * @return the string representation of this polynomial
     */
    public String toString() {
        StringBuffer sb = new StringBuffer(4096);

        sb.append("p");
        sb.append(p.toString());
        sb.append("g");
        sb.append(g.toString());
        sb.append("f");
        sb.append(f.toString());

        /*for (AdderInteger c : coeffs) {*/
        for (Iterator it = coeffs.iterator(); it.hasNext();) {
            AdderInteger c = (AdderInteger) it.next();
            sb.append(" ");
            sb.append(c.toString());
        }

        return sb.toString();
    }
}
