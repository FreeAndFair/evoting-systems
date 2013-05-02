package edu.uconn.cse.adder;

/**
 * Thrown by the <tt>getFinalSum</tt> method of a <code>Election</code>
 * to indicate that the search space has been exhausted.
 *
 * @author  David Walluck
 * @version $LastChangedRevision$ $LastChangedDate$
 * @see     Election
 * @see     Election#getFinalSum
 * @since   0.0.1
 */
public class SearchSpaceExhaustedException extends RuntimeException {
    private static final long serialVersionUID = 0L;

    /**
     * Constructs an <code>SearchSpaceExhaustedException</code> with
     * <tt>null</tt> as its error message string.
     */
    public SearchSpaceExhaustedException() {
        super();
    }

    /**
     * Constructs a <code>SearchSpaceExhaustedException</code>, saving a
     * reference to the error message string <tt>s</tt> for later retrieval by
     * the <tt>getMessage</tt> method.
     *
     * @param s the detail message
     */
    public SearchSpaceExhaustedException(String s) {
        super(s);
    }
}
