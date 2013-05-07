package edu.uconn.cse.adder;

/**
 * Thrown by the <tt>fromString</tt> method of a <code>ElgamalCiphertext</code>
 * to indicate that there was a parse error.
 *
 * @author  David Walluck
 * @version $LastChangedRevision$ $LastChangedDate$
 * @see     ElgamalCiphertext
 * @see     ElgamalCiphertext#fromString(String)
 * @since   0.0.1
 */
public class InvalidElgamalCiphertextException extends RuntimeException {
    private static final long serialVersionUID = 0L;

    /**
     * Constructs an <code>InvalidElgamalCiphertextException</code> with
     * <tt>null</tt> as its error message string.
     */
    public InvalidElgamalCiphertextException() {
        super();
    }

    /**
     * Constructs a <code>InvalidElgamalCiphertextException</code>, saving a reference
     * to the error message string <tt>s</tt> for later retrieval by the
     * <tt>getMessage</tt> method.
     *
     * @param s the detail message
     */
    public InvalidElgamalCiphertextException(String s) {
        super(s);
    }
}
