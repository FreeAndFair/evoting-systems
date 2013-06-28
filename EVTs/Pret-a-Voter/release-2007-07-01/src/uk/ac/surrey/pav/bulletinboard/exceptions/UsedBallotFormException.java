package uk.ac.surrey.pav.bulletinboard.exceptions;

/**
 * This is thrown if a booth submits to the web bulletin board a
 * ballot form that has been used to cast a vote or has been cancelled
 * for one reason or another.
 * 
 * @author David Lundin
 *
 */
public class UsedBallotFormException extends LoggedException {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	
	/**
	 * Default constructor
	 *
	 */
	public UsedBallotFormException() {
		
	}
	
	/**
	 * Default constructor
	 * 
	 * @param s A message
	 */
	public UsedBallotFormException(String s) {
		super(s);
	}

}
