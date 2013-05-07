package edu.uconn.cse.adder;

/**
 * Thrown by the <tt>fromString</tt> method of a <code>MembershipProof</code>
 * to indicate that there was a parse error.
 *
 * @author  David Walluck
 * @version $LastChangedRevision$ $LastChangedDate$
 * @see     MembershipProof
 * @see     MembershipProof#fromString(String)
 * @since   0.0.1
 */
public class InvalidMembershipProofException extends RuntimeException {
    private static final long serialVersionUID = 0L;

    /**
     * Constructs an <code>InvalidMembershipProofException</code> with
     * <tt>null</tt> as its error message string.
     */
    public InvalidMembershipProofException() {
        super();
    }

    /**
     * Constructs a <code>InvalidMembershipProofException</code>, saving a reference
     * to the error message string <tt>s</tt> for later retrieval by the
     * <tt>getMessage</tt> method.
     *
     * @param s the detail message
     */
    public InvalidMembershipProofException(String s) {
        super(s);
    }
}
