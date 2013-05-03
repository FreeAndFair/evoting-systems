package edu.uconn.cse.adder.test;

import java.math.BigInteger;

import junit.framework.TestCase;
import junit.textui.TestRunner;
import edu.uconn.cse.adder.AdderInteger;

/**
 * Adder integer test.
 *
 * @author David Walluck
 * @version $LastChangedRevision$ $LastChangedDate$
 * @since 0.0.1
 */
public class AdderIntegerTest extends TestCase {
    /**
     * Constructs a new adder integer test.
     *
     * @param name the name of the test
     */
    public AdderIntegerTest(String name) {
        super(name);
    }

    /**
     * Test.
     */
    public void test() {
        AdderInteger p = new AdderInteger("23", "11");

        assertEquals(AdderInteger.ONE, p);
        System.out.println("p = " + p);

        AdderInteger pMinusOne = p.subtract(AdderInteger.ONE);
        assertEquals(AdderInteger.ZERO, pMinusOne);
        System.out.println("p - 1 = " + pMinusOne);

        AdderInteger pMinusOneOverTwo = p.subtract(AdderInteger.ONE)
                                          .divide(AdderInteger.TWO);
        assertEquals(AdderInteger.ZERO, pMinusOneOverTwo);
        System.out.println("(p - 1) / 2 = " + pMinusOneOverTwo);

        AdderInteger pPlusFive = p.add(new AdderInteger("5"));
        assertEquals(new AdderInteger("6"), pPlusFive);
        System.out.println("p + 5 = " + pPlusFive);

        AdderInteger pTimesEight = p.multiply(new AdderInteger("8"));
        assertEquals(new AdderInteger("8"), pTimesEight);
        System.out.println("p * 8 = " + pTimesEight);

        AdderInteger negativeP = p.negate();
        assertEquals(new AdderInteger("10"), negativeP);
        System.out.println("-p = " + negativeP);

        AdderInteger x = new AdderInteger(1, 10);
        assertEquals(new AdderInteger("1"), x.getValue());

        //AdderInteger y = new AdderInteger(BigInteger.ONE, BigInteger.TEN);
        AdderInteger y = new AdderInteger(BigInteger.ONE, new BigInteger("10"));
        assertEquals(new AdderInteger("1"), y.getValue());

        AdderInteger z = AdderInteger.random("10");
        assertTrue(z.getValue().compareTo(new AdderInteger("10")) < 0
                   && z.getValue().compareTo(AdderInteger.ZERO) >= 0);

        //AdderInteger w = AdderInteger.random(BigInteger.TEN);
        AdderInteger w = AdderInteger.random(new BigInteger("10"));
        assertTrue(w.getValue().compareTo(new AdderInteger("10")) < 0
                   && w.getValue().compareTo(AdderInteger.ZERO) >= 0);

        //assertFalse(w.equals(""));

        AdderInteger v = new AdderInteger("15");
        assertEquals("15", v.toString(10));
        assertEquals("f", v.toString(16));
    }

    /**
     * The main method.
     *
     * @param args the main parameters
     */
    public static void main(String[] args) {
        TestRunner.run(AdderTest.class);
    }
}
