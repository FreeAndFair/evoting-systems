package edu.uconn.cse.adder.test;

import junit.framework.TestCase;
import junit.textui.TestRunner;
import edu.uconn.cse.adder.AdderInteger;
import edu.uconn.cse.adder.InvalidPolynomialException;
import edu.uconn.cse.adder.Polynomial;

/**
 * Polynomial test.
 *
 * @version $LastChangedRevision$ $LastChangedDate$
 * @since 0.0.1
 * @author David Walluck
 */
public class PolynomialTest extends TestCase {
    /**
     * Constructs a new polynomial test.
     *
     * @param name the name of the test
     */
    public PolynomialTest(String name) {
        super(name);
    }

    /**
     * The test.
     */
    public void test() {
        try {
            Polynomial poly = Polynomial.fromString("p123g135f246");

            assertEquals(new AdderInteger("123"), poly.getP());
            assertEquals(new AdderInteger("135", poly.getP()), poly.getG());
            assertEquals(new AdderInteger("246", poly.getP()), poly.getF());
        } catch (InvalidPolynomialException ipe) {
            fail();
        }

        Polynomial poly1 = new Polynomial(new AdderInteger("123"),
                                          new AdderInteger("135"),
                                          new AdderInteger("246"));

        assertEquals(new AdderInteger("123"), poly1.getP());
        assertEquals(new AdderInteger("135"), poly1.getG());
        assertEquals(new AdderInteger("246"), poly1.getF());

        try {
            Polynomial.fromString("pgf");
            fail();
        } catch (InvalidPolynomialException ive) {

        }

        try {
            Polynomial.fromString("p123g123f12a");
            fail();
        } catch (InvalidPolynomialException ive) {

        }

        try {
            Polynomial.fromString("p123g123f123p123");
            fail();
        } catch (InvalidPolynomialException ive) {

        }

        try {
            Polynomial poly2 =
                Polynomial.fromString("p123g123f123 123 333 123");
            assertEquals(3, poly2.getCoeffs().size());
            assertEquals(new AdderInteger("28"),
                                          (AdderInteger)
                                          poly2.getCoeffs().get(1));
            assertEquals(2, poly2.getDegree());
            assertEquals("p123g0f0 1 28 1", poly2.toString());
        } catch (InvalidPolynomialException ive) {
            fail();
        }

        Polynomial poly3 = new Polynomial(new AdderInteger("123"),
                                          new AdderInteger("135"),
                                          new AdderInteger("246"), 1);

        assertEquals(2, poly3.getCoeffs().size());
        assertEquals(1, poly3.getDegree());

        try {
            Polynomial poly4 =
                Polynomial.
                fromString("p968689912559g677313859426f927938857925"
                           + " 382444364348");

            assertEquals(new AdderInteger("382444364348"),
                         poly4.evaluate(new AdderInteger(4)));
        } catch (InvalidPolynomialException ipe) {
            fail();
        }

        try {
            Polynomial.fromString("p123g135");
            fail();
        } catch (InvalidPolynomialException ipe) {

        }

        try {
            Polynomial.fromString("g123g135f246");
            fail();
        } catch (InvalidPolynomialException ipe) {

        }

        try {
            Polynomial.fromString("p123p135f246");
            fail();
        } catch (InvalidPolynomialException ipe) {

        }

        try {
            Polynomial.fromString("p123g135g246");
            fail();
        } catch (InvalidPolynomialException ipe) {

        }

        try {
            Polynomial.fromString("p123g135f246 xyz");
            fail();
        } catch (InvalidPolynomialException ipe) {

        }
    }

    /**
     * The main method.
     *
     * @param args the main parameters
     */
    public static void main(String[] args) {
        TestRunner.run(PolynomialTest.class);
    }
}
