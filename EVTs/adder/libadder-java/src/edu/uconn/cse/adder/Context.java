package edu.uconn.cse.adder;

import java.security.NoSuchAlgorithmException;
import java.security.SecureRandom;
import java.util.Random;


/**
 * Encapsulates random number generator used by the <code>AdderInteger</code>
 * class.
 *
 * @author  David Walluck
 * @version $LastChangedRevision$ $LastChangedDate$
 * @see     AdderInteger
 * @see     AdderInteger#random(AdderInteger)
 * @see     AdderInteger#random(int)
 * @see     AdderInteger#random(String)
 * @see     AdderInteger#random(java.math.BigInteger)
 * @since   0.0.1
 */
public final class Context {
    private Random random;

    /**
     * Create a Context.
     */
    public Context() {
        try {
            random = SecureRandom.getInstance("SHA1PRNG");
        } catch (NoSuchAlgorithmException nsae) {
            throw new RuntimeException(nsae);
        }
    }

   /**
    * Gets the random number generator used by this context.
    *
    * @return the random number generator
    */
    public Random getRandom() {
        return random;
    }

   /**
    * Checks this context to determine whether or not
    * the context is secure.
    *
    * @return <tt>true</tt> if the context is secure
    */
    public boolean isSecure() {
        return true;
    }
}
