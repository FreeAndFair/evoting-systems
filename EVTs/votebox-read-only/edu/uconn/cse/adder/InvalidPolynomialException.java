package edu.uconn.cse.adder;

/**
 * Thrown by the <tt>fromString</tt> method of a <code>Polynomial</code>
 * to indicate that there was a parse error.
 *
 * @author  David Walluck
 * @version $LastChangedRevision$ $LastChangedDate$
 * @see     Polynomial
 * @see     Polynomial#fromString(String)
 * @since   0.0.1
 */
public class InvalidPolynomialException extends RuntimeException {
    private static final long serialVersionUID = 0L;

    /**
     * Constructs an <code>InvalidPolynomialException</code> with
     * <tt>null</tt> as its error message string.
     */
    public InvalidPolynomialException() {
        super();
    }

    /**
     * Constructs a <code>InvalidPolynomialException</code>, saving a reference
     * to the error message string <tt>s</tt> for later retrieval by the
     * <tt>getMessage</tt> method.
     *
     * @param s the detail message
     */
    public InvalidPolynomialException(String s) {
        super(s);
    }
}
