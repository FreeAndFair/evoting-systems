package edu.uconn.cse.adder.test;

import junit.framework.Test;
import junit.framework.TestSuite;
import junit.textui.TestRunner;

/**
 * All tests.
 *
 * @version $LastChangedRevision$ $LastChangedDate$
 * @since 0.0.1
 * @author David Walluck
 */
public class AllTests {
    /**
     * Constructs a new test suite.
     *
     * @return the test
     */
    public static Test suite() {
        TestSuite suite = new TestSuite();

        suite.addTest(new TestSuite(ContextTest.class));
        //suite.addTest(new TestSuite(ElgamalCiphertextTest.class));
        //suite.addTest(new TestSuite(MembershipProofTest.class));
        suite.addTest(new TestSuite(PolynomialTest.class));
        suite.addTest(new TestSuite(PluginTest.class));
        suite.addTest(new TestSuite(PrivateKeyTest.class));
        suite.addTest(new TestSuite(PublicKeyTest.class));
        suite.addTest(new TestSuite(VoteTest.class));
        suite.addTest(new TestSuite(AdderTest.class));

        return suite;
    }

    /**
     * The main method.
     *
     * @param args the main parameters
     */
    public static void main(String[] args) {
        TestRunner.run(suite());
    }
}

