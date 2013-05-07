package edu.uconn.cse.adder.test;

import junit.framework.TestCase;
import junit.textui.TestRunner;
import edu.uconn.cse.adder.AdderInteger;
import edu.uconn.cse.adder.InvalidPublicKeyException;
import edu.uconn.cse.adder.PublicKey;

/**
 * Public key test.
 *
 * @version $LastChangedRevision$ $LastChangedDate$
 * @since 0.0.1
 * @author David Walluck
 */
public class PublicKeyTest extends TestCase {
    /**
     * Constructs a new public key test.
     *
     * @param name the name of the test.
     */
    public PublicKeyTest(String name) {
        super(name);
    }

    /**
     * The test.
     */
    public void test() {
        try {
            PublicKey publicKey = PublicKey.fromString("p123g135h246f234");

            assertEquals(new AdderInteger("123"), publicKey.getP());
            assertEquals(new AdderInteger("135", publicKey.getP()),
                         publicKey.getG());
            assertEquals(new AdderInteger("246", publicKey.getP()),
                         publicKey.getH());
            assertEquals(new AdderInteger("234", publicKey.getP()),
                         publicKey.getF());
        } catch (InvalidPublicKeyException ipke) {
            fail();
        }

        PublicKey publicKey1 = new PublicKey(new AdderInteger("123"),
                                                new AdderInteger("135"),
                                                new AdderInteger("246"),
                                                new AdderInteger("234"));

        assertEquals(new AdderInteger("123"), publicKey1.getP());
        assertEquals(new AdderInteger("135"), publicKey1.getG());
        assertEquals(new AdderInteger("246"), publicKey1.getH());
        assertEquals(new AdderInteger("234"), publicKey1.getF());

        PublicKey publicKey2 = new PublicKey(new AdderInteger("123"),
                                                new AdderInteger("135"),
                                                new AdderInteger("246"),
                                                new AdderInteger("234"));

        assertEquals("p123g135h246f234", publicKey2.toString());

        try {
            PublicKey.fromString("pghf");
            fail();
        } catch (InvalidPublicKeyException ipke) {

        }

        try {
            PublicKey.fromString("p123g123h123f12a");
            fail();
        } catch (InvalidPublicKeyException ipke) {

        }

        try {
            PublicKey.fromString("p123g123h123p123");
            fail();
        } catch (InvalidPublicKeyException ipke) {

        }

        try {
            PublicKey.fromString("g123g123h123p123");
            fail();
        } catch (InvalidPublicKeyException ipke) {

        }

        try {
            PublicKey.fromString("p123h123h123p123");
            fail();
        } catch (InvalidPublicKeyException ipke) {

        }

        try {
            PublicKey.fromString("p123g123g123");
            fail();
        } catch (InvalidPublicKeyException ipke) {

        }

        try {
            PublicKey.fromString("p123g135h246f234p123");
            fail();
        } catch (InvalidPublicKeyException ipke) {

        }
    }

    /**
     * The main method.
     *
     * @param args the main parameters
     */
    public static void main(String[] args) {
        TestRunner.run(PublicKeyTest.class);
    }
}
