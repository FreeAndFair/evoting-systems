package edu.uconn.cse.adder;

import java.math.BigInteger;

import sexpression.ASExpression;
import sexpression.ListExpression;
import sexpression.StringExpression;

/**
 * Arbitrary-precision integers for modular arithmetic.
 * Internally, Java's BigInteger class is used to represent the
 * value and the modulus.
 *
 * @author David Walluck
 * @see BigInteger
 * @version $LastChangedRevision$ $LastChangedDate$
 * @since 0.0.1
 */
public class AdderInteger implements Comparable/*<AdderInteger>*/ {
    /**
     * The AdderInteger constant zero.
     */
    public static final AdderInteger ZERO = new AdderInteger("0");
    /**
     * The AdderInteger constant one.
     */
    public static final AdderInteger ONE = new AdderInteger("1");
    /**
     * The AdderInteger constant two.
     */
    public static final AdderInteger TWO = new AdderInteger("2");

    private BigInteger val;
    private BigInteger m;
    private static final Context CTX = new Context();


    /**
     * Creates an AdderInteger with value and modulus of zero.
     */
    public AdderInteger() {
        this.val = BigInteger.ZERO;
        this.m = BigInteger.ZERO;
    }

    /**
     * Copies the the given AdderInteger into this AdderInteger.
     *
     * @param b AdderInteger to be copied
     */
    public AdderInteger(AdderInteger b) {
        this.val = b.val;
        this.m = b.m;
    }

    /**
     * Translates the integer representation of AdderInteger into an
     * AdderInteger. The integer is converted into a String and then
     * into a BigInteger.
     *
     * @param val int representation of AdderInteger
     * @see   BigInteger
     */
    public AdderInteger(int val) {
        this.val = new BigInteger(Integer.toString(val));
        this.m = BigInteger.ZERO;
    }

    /**
     * Translates the String representation of an AdderInteger in the specified
     * base into an AdderInteger. The String representation consists of the same
     * format as BigInteger.
     *
     * @param val String representation of AdderInteger
     * @param base base to be used in interpreting <tt>val</tt>
     * @see   BigInteger
     */
    public AdderInteger(String val, int base) {
        this.val = new BigInteger(val, base);
        this.m = BigInteger.ZERO;
    }

    /**
     * Translates the decimal BigInteger representation of an AdderInteger with
     * the given modulus into an AdderInteger. The String representation
     * consists of the same format as BigInteger.
     *
     * @param val String representation of AdderInteger
     * @param m   the modulus
     * @see   BigInteger
     */
    public AdderInteger(BigInteger val, BigInteger m) {
        this.val = val;
        this.m = m;
        this.val = this.val.mod(m);
    }

    /**
     * Translates the String representation of an AdderInteger in the specified
     * base and the given modulus into an AdderInteger. The String
     * representation consists of the same format as BigInteger.
     *
     * @param val  String representation of AdderInteger
     * @param m    the modulus
     * @param base base to be used in interpreting <tt>val</tt>
     * @see   BigInteger
     */
    public AdderInteger(String val, AdderInteger m, int base) {
        this.val = new BigInteger(val, base).mod(m.val);
        this.m = m.val;
    }

    /**
     * Translates the integer representation of AdderInteger with the given
     * modulus into an AdderInteger. The integer is converted into a String
     * and then into a BigInteger.
     *
     * @param val int representation of AdderInteger
     * @param m the modulus
     * @see   BigInteger
     */
    public AdderInteger(int val, int m) {
        BigInteger v = new BigInteger(Integer.toString(val));
        BigInteger mv = new BigInteger(Integer.toString(m));

        this.val = v;
        this.m = mv;
        this.val = this.val.mod(mv);
    }

    //////////

    /**
     * Translates the decimal BigInteger representation of an AdderInteger into
     * an AdderInteger. The String representation consists of the same format as
     * BigInteger.
     *
     * @param val String representation of AdderInteger
     * @see   BigInteger
     */
    public AdderInteger(BigInteger val) {
        this.val = val;
        this.m = BigInteger.ZERO;
    }

    /**
     * Translates the decimal String representation of an AdderInteger into an
     * AdderInteger.  The String representation consists of consists of the
     * same format as BigInteger.
     *
     * @param val decimal String representation of AdderInteger
     * @see   BigInteger
     */
    public AdderInteger(String val) {
        this(val, 10);
    }

    /**
     * Translates the int representation of an AdderInteger into an
     * AdderInteger. The String representation consists of consists of the same
     * format as BigInteger.
     *
     * @param val decimal String representation of BigInteger.
     * @param m the modulus
     * @see   BigInteger
     */
    public AdderInteger(int val, AdderInteger m) {
        this(Integer.toString(val), m, 10);
    }

    /**
     * Translates the decimal String representation of an AdderInteger with the
     * specified modulus into an AdderInteger. The String representation
     * consists of consists of the same format as BigInteger.
     *
     * @param val decimal String representation of BigInteger
     * @param m   the modulus
     * @see   BigInteger
     */
    public AdderInteger(String val, AdderInteger m) {
        this(val, m, 10);
    }

    /**
     * Translates the decimal String representation of an AdderInteger with the
     * specified modulus into an AdderInteger. The String representation
     * consists of consists of the same format as BigInteger.
     *
     * @param val decimal String representation of BigInteger
     * @param m   the modulus
     */
    public AdderInteger(String val, String m) {
        this(val, new AdderInteger(m));
    }

    /**
     * Copies the the given AdderInteger and modulus into this AdderInteger.
     *
     * @param b AdderInteger to be copied
     * @param m the modulus
     * @see   #toString()
     */
    public AdderInteger(AdderInteger b, AdderInteger m) {
        this(b.toString(), m);
    }

    //////////

    /**
     * Returns whether this AdderInteger is value is divisible by the given
     * AdderInteger.
     *
     * @param  b value by which divisibility is to be computed.
     * @return <tt>true</tt> if divisible by the given AdderInteger
     */
    public boolean isDivisible(AdderInteger b) {
        return val.remainder(b.val).equals(BigInteger.ZERO);
    }

    /**
     * Gets the value of this AdderInteger.
     *
     * @return the value
     */
    public AdderInteger getValue() {
        return new AdderInteger(val);
    }

    /**
     * Gets the modulus of this AdderInteger.
     *
     * @return the modulus
     */
    public AdderInteger getModulus() {
        return new AdderInteger(m);
    }

    /**
     * Returns a randomly generated AdderInteger, uniformly distributed over
     * the range <tt>0</tt> to <tt>(n - 1)</tt>, inclusive.
     * The uniformity of the distribution should be uniform, as a secure source
     * of randomness is used. Note that this method always returns a
     * non-negative AdderInteger.
     *
     * @param  n the bound for the new AdderInteger
     * @return the new AdderInteger
     */
    public static AdderInteger random(AdderInteger n) {
        BigInteger t;

        do {
            t = new BigInteger(n.val.bitLength(), CTX.getRandom());
        } while (t.compareTo(n.val) >= 0);

        AdderInteger c = new AdderInteger();

        c.m = n.val;

        c.val = t;

        return c;
    }

    /**
     * Returns a randomly generated int, uniformly distributed over
     * the range <tt>a</tt> to <tt>(b - 1)</tt>, inclusive.
     * The uniformity of the distribution should be uniform, as a secure source
     * of randomness is used.
     *
     * @param  a the lower bound for the new int
     * @param  b the upper bound for the new int
     * @return the new int
     */
    public static int random(int a, int b) {
         return CTX.getRandom().nextInt(b - a) + a;
    }

    /**
     * Returns a randomly generated AdderInteger, uniformly distributed over
     * the range <tt>0</tt> to <tt>(n - 1)</tt>, inclusive.
     * The uniformity of the distribution should be uniform, as a secure source
     * of randomness is used. Note that this method always returns a
     * non-negative AdderInteger.
     *
     * @param  n the bound for the new AdderInteger
     * @return the new AdderInteger
     */
    public static AdderInteger random(int n) {
        return random(new AdderInteger(n));
    }

    /**
     * Returns a randomly generated AdderInteger, uniformly distributed over
     * the range <tt>0</tt> to <tt>(n - 1)</tt>, inclusive.
     * The uniformity of the distribution should be uniform, as a secure source
     * of randomness is used. Note that this method always returns a
     * non-negative AdderInteger.
     *
     * @param  n the bound for the new AdderInteger
     * @return the new AdderInteger
     */
    public static AdderInteger random(String n) {
        return random(new AdderInteger(n));
    }

    /**
     * Returns a randomly generated AdderInteger, uniformly distributed over
     * the range <tt>0</tt> to <tt>(n - 1)</tt>, inclusive.
     * The uniformity of the distribution should be uniform, as a secure source
     * of randomness is used. Note that this method always returns a
     * non-negative AdderInteger.
     *
     * @param  n the bound for the new AdderInteger
     * @return the new AdderInteger
     */
    public static AdderInteger random(BigInteger n) {
        return random(new AdderInteger(n));
    }

    /**
     * Returns a positive AdderInteger that is probably a safe prime, with
     * the specified bitLength. The probability that an AdderInteger returned
     * by this method is composite does not exceed 2<sup>-100</sup>.
     *
     * @param  bitLength bitLength of the returned BigInteger.
     * @return an AdderInteger of <tt>bitLength</tt> bits that is probably
               a safe prime
     * @see    BigInteger#bitLength()
     */
    public static AdderInteger safePrime(int bitLength) {
        final BigInteger two = new BigInteger("2");
        BigInteger p;
        BigInteger q;

        do {
            p = BigInteger.probablePrime(bitLength, CTX.getRandom());
            q = p.subtract(BigInteger.ONE).divide(two);
        } while (!q.isProbablePrime(100));

        return new AdderInteger(p);
    }

    /**
     * Returns an AdderInteger whose value is <tt>(-this)</tt>.
     *
     * @return <tt>-this</tt>
     */
    public AdderInteger negate() {
        AdderInteger c = new AdderInteger();

        if (!m.equals(BigInteger.ZERO)) {
            c.val = m.subtract(val);
        } else {
            c.val = val.negate();
        }

        return c;
    }

    /**
     * Returns an AdderInteger whose value is <tt>(this + val)</tt>.
     *
     * @param  b value to be added to this AdderInteger
     * @return <tt>this + val</tt>
     */
    public AdderInteger add(AdderInteger b) {
        AdderInteger c = new AdderInteger();

        c.m = m;

        c.val = val.add(b.val);

        if (!m.equals(BigInteger.ZERO)) {
            c.val = c.val.mod(c.m);
        }

        return c;
    }

    /**
     * Returns an AdderInteger whose value is <tt>(this - val)</tt>.
     *
     * @param  b value to be subtracted to this AdderInteger
     * @return <tt>this - val</tt>
     */
    public AdderInteger subtract(AdderInteger b) {
        AdderInteger c = new AdderInteger();

        c.m = m;

        if (!m.equals(BigInteger.ZERO)) {
            c.val = val.add((b.negate()).val);
        } else {
            c.val = val.subtract(b.val);
        }

        return c;
    }

    /**
     * Returns an AdderInteger whose value is <tt>(this * val)</tt>.
     *
     * @param  b value to be multiplied by this AdderInteger
     * @return <tt>this * val</tt>
     */
    public AdderInteger multiply(AdderInteger b) {
        AdderInteger c = new AdderInteger();

        c.m = m;

        c.val = val.multiply(b.val);

        if (!m.equals(BigInteger.ZERO)) {
            c.val = c.val.mod(c.m);
        }

        return c;
    }

    /**
     * Returns an AdderInteger whose value is <tt>(this / val)</tt>.
     *
     * @param  b value to be divided
     * @return <tt>this / val</tt>
     */
    public AdderInteger divide(AdderInteger b) {
        AdderInteger c = new AdderInteger();

        c.m = m;

        if (!m.equals(BigInteger.ZERO)) {
            BigInteger bInv = b.val.modInverse(m);
            c.val = val.multiply(bInv);
            c.val = c.val.mod(c.m);
        } else {
            c.val = val.divide(b.val);
        }

        return c;
    }

    /**
     * Returns an AdderInteger whose value is <tt>(this mod m</tt>).
     *
     * @param  m the modulus.
     * @return <tt>this mod m</tt>
     */
    public AdderInteger mod(AdderInteger m) {
        AdderInteger c = new AdderInteger();

        c.m = this.m;

        c.val = val.mod(m.val);

        return c;
    }

    /**
     * Returns an AdderInteger whose value is
     * <tt>(this<sup>exponent</sup>)</tt>.
     *
     * @param  exponent exponent to which this AdderInteger is to be raised.
     * @return <tt>this<sup>exponent</sup></tt>
     */
    public AdderInteger pow(AdderInteger exponent) {
        AdderInteger c = new AdderInteger();

        c.m = m;

        if (!m.equals(BigInteger.ZERO)) {
            c.val = val.modPow(exponent.val, c.m);
        } else {
            c.val = val.pow(exponent.val.intValue());
        }

        return c;
    }

    /**
     * Returns an AdderInteger whose value is
     * <tt>(this<sup>exponent</sup>)</tt>. Note that <tt>exponent</tt>
     * is an integer rather than an AdderInteger.
     *
     * @param  exponent exponent to which this AdderInteger is to be raised.
     * @return <tt>this<sup>exponent</sup></tt>
     */
    public AdderInteger pow(int exponent) {
        return pow(new AdderInteger(exponent));
    }

    /**
     * Compares this AdderInteger with the specified AdderInteger. This method
     * is provided in preference to individual methods for each of the six
     * boolean comparison operators (&lt;, ==, &gt;, &gt;=, !=, &lt;=). The
     * suggested idiom for performing these comparisons is:
     * <tt>(x.compareTo(y)</tt> &lt;<i>op</i>&gt; <tt>0)</tt>,
     * where &lt;<i>op</i>&gt; is one of the six comparison operators.
     *
     * @param  b AdderInteger to which this AdderInteger is to be compared.
     * @return -1, 0 or 1 as this BigInteger is numerically less than, equal
     *         to, or greater than <tt>b</tt>
     */
    public int compareTo(Object b) {
        return val.compareTo(((AdderInteger) b).val);
    }

    /**
     * Returns the hash code for this AdderInteger.
     *
     * @return hash code for this AdderInteger
     */
    public int hashCode() {
        return val.hashCode() | m.hashCode();
    }

    /**
     * Compares this AdderInteger with the specified Object for equality.
     *
     * @param  x Object to which this AdderInteger is to be compared
     * @return <tt>true</tt> if and only if the specified Object is a
     *         AdderInteger whose value is numerically equal to this
     *         AdderInteger's value.
     */
    public boolean equals(Object x) {
        if (x == this) {
            return true;
        }

        if (!(x instanceof AdderInteger)) {
            return false;
        }

        return val.equals(((AdderInteger) x).val);
    }

   /**
    * Converts this AdderInteger to an <tt>int</tt>. This
    * conversion is equivalent to BigInteger.
    *
    * @return this AdderInteger converted to an <tt>int</tt>
    * @see    BigInteger#intValue()
    */
    public int intValue() {
        return val.intValue();
    }

   /**
    * Converts this AdderInteger to a BigInteger.
    *
    * @return this AdderInteger converted to a BigInteger
    * @see    BigInteger
    */
    public BigInteger bigintValue() {
        return val;
    }

    /**
     * Returns the String representation of this AdderInteger in the default
     * base of ten. This follows the same rules as BigInteger.
     *
     * @return String representation of this BigInteger in the given radix.
     * @see    Integer#toString()
     * @see    BigInteger#toString()
     */
    public String toString() {
        return val.toString();
    }

    /**
     * Returns the String representation of this AdderInteger in the given
     * base. This follows the same rules as BigInteger.
     *
     * @param  base base of the String representation
     * @return String representation of this BigInteger in the given radix.
     * @see    Integer#toString()
     * @see    BigInteger#toString(int)
     */
    public String toString(int base) {
        return val.toString(base);
    }
 
    /**
     * Method for interop with VoteBox's S-Expression system.
     * 
     * @return the S-Expression equivalent of this AdderInteger
     */
    public ASExpression toASE(){
    	return new ListExpression(StringExpression.makeString("adder-integer"), StringExpression.makeString(""+getValue()), StringExpression.makeString(""+getModulus()));
    }
    
    /**
     * Method for interop with VoteBox's S-Expression system.
     * 
     * @return the S-Expression equivalent of this AdderInteger
     */
    public static AdderInteger fromASE(ASExpression ase){
    	ListExpression list = (ListExpression)ase;
    	
    	if(list.size() != 3)
    		throw new RuntimeException("Not an adder-integer");
    	
    	if(!list.get(0).toString().equals("adder-integer"))
    		throw new RuntimeException("Not an adder-integer");
    	
    	BigInteger v = new BigInteger(list.get(1).toString());
    	BigInteger m = new BigInteger(list.get(2).toString());
    	
    	if(!m.equals(BigInteger.ZERO))
    		return new AdderInteger(v, m);
    	
    	return new AdderInteger(v);
    }
}
