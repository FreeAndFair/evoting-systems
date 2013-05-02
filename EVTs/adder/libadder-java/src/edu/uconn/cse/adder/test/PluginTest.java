package edu.uconn.cse.adder.test;

import junit.framework.TestCase;
import junit.textui.TestRunner;
import edu.uconn.cse.adder.InvalidPublicKeyException;
import edu.uconn.cse.adder.plugin.Plugin;

/**
 * Plugin test.
 *
 * @version $LastChangedRevision$ $LastChangedDate$
 * @since 0.0.1
 * @author David Walluck
 */
public class PluginTest extends TestCase {
    /**
     * Constructs a new plugin test.
     *
     * @param name the name of the test
     */
    public PluginTest(String name) {
        super(name);
    }

    /**
     * The test.
     */
    public void test() {
        try {
            String serverPublicKey
                = "p856084772267g627785624102h42922417776f597922918700";
            String vote = "1";

            String encryptedVote = Plugin.encryptVote(serverPublicKey,
                                                      vote, 1, 1);

            System.out.println("Encrypted vote is " + encryptedVote);

            String user = "adder";
            String procedure = "a6a8ddae-3154-4243-82df-cbd0334686b8";

            boolean createdKeyPair = Plugin.createKeyPair(user, procedure,
                                                          serverPublicKey,
                                                          true);

            assertTrue(createdKeyPair);

            String pubKey = Plugin.readPubKey(user, procedure);

            assertNotNull(pubKey);

            System.out.println("Read public key " + pubKey);
        } catch (InvalidPublicKeyException ipke) {
            fail();
        }
    }

    /**
     * The main method.
     *
     * @param args the main parameters
     */
    public static void main(String[] args) {
        TestRunner.run(PluginTest.class);
    }
}
