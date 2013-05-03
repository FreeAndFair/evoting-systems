package edu.uconn.cse.adder;

/**
 * Thrown by the <tt>fromString</tt> method of a <code>Vote</code>
 * to indicate that there was a parse error.
 *
 * @author  David Walluck
 * @version $LastChangedRevision$ $LastChangedDate$
 * @see     Vote
 * @see     Vote#fromString(String)
 * @since   0.0.1
 */
public class InvalidVoteException extends RuntimeException {
    private static final long serialVersionUID = 0L;

    /**
     * Constructs an <code>InvalidVoteException</code> with
     * <tt>null</tt> as its error message string.
     */
    public InvalidVoteException() {
        super();
    }

    /**
     * Constructs a <code>InvalidVoteException</code>, saving a reference
     * to the error message string <tt>s</tt> for later retrieval by the
     * <tt>getMessage</tt> method.
     *
     * @param s the detail message
     */
    public InvalidVoteException(String s) {
        super(s);
    }
}
