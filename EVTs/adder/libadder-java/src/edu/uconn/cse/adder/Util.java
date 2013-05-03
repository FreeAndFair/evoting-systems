package edu.uconn.cse.adder;

import java.io.UnsupportedEncodingException;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;

/**
 * Miscelaneous static utility methods.
 *
 * @author David Walluck
 * @version $LastChangedRevision$ $LastChangedDate$
 * @since 0.0.1
 */
public final class Util {
    /** Don't instantiate me! */
    private Util() {

    }

    /**
     * Convert a byte array into the corresponding string.
     *
     * @param  b the byte array to convert
     * @return the string representation of this byte array
     */
    public static String byteArrayToHexString(byte[] b) {
        StringBuffer sb = new StringBuffer(b.length * 2);

        for (int i = 0; i < b.length; i++) {
            int j = (b[i] & 0xff);

            if (j < 16) {
                sb.append('0');
            }

            sb.append(Integer.toHexString(j));
        }

        return sb.toString();
    }

    /**
     * Computes the SHA1 sum of the given string.
     *
     * @param s the string
     * @return the SHA1 sum
     */
    public static String sha1(String s) {
        try {
            return byteArrayToHexString(MessageDigest
                                        .getInstance("SHA")
                                        .digest(s.getBytes("US-ASCII")));
        } catch (NoSuchAlgorithmException nsae) {
            throw new RuntimeException(nsae);
        } catch (UnsupportedEncodingException uee) {
            throw new RuntimeException(uee);
        }
    }

    /**
     * Determines whether the given character is a hexidecimal digit.
     *
     * @param c the character
     * @return <tt>true</tt> if the given character is a valid digit
     */
    public static boolean isHexDigit(char c) {
        return ((c >= '0' && c <= '9')
                || ((c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F')));
    }
}
