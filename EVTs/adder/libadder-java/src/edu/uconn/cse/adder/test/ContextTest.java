package edu.uconn.cse.adder.test;

import java.security.SecureRandom;

import junit.framework.TestCase;
import junit.textui.TestRunner;
import edu.uconn.cse.adder.Context;

/**
 * Context test.
 *
 * @version $LastChangedRevision$ $LastChangedDate$
 * @since 0.0.1
 * @author David Walluck
 */
public class ContextTest extends TestCase {
    /**
     * Constructs a new context test.
     *
     * @param name the name of the test
     */
    public ContextTest(String name) {
        super(name);
    }

    /**
     * The test.
     */
    public void test() {
        Context c1 = new Context();

        assertNotNull(c1.getRandom());
        assertTrue(c1.getRandom() instanceof SecureRandom);
        assertEquals(true, c1.isSecure());
    }

    /**
     * The main method.
     *
     * @param args the main parameters
     */
    public static void main(String[] args) {
        TestRunner.run(ContextTest.class);
    }
}
