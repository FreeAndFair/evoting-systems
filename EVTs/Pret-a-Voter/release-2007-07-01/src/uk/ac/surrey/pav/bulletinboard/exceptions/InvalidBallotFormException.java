package uk.ac.surrey.pav.bulletinboard.exceptions;

/**
 * This is thrown when anything is wrong with the ballot form
 * or a ballot form cannot be found in the database.
 * 
 * @author David Lundin
 *
 */
public class InvalidBallotFormException extends LoggedException {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	
	/**
	 * Default constructor
	 *
	 */
	public InvalidBallotFormException() {
		
	}
	
	/**
	 * Default constructor
	 * 
	 * @param s A message
	 */
	public InvalidBallotFormException(String s) {
		super(s);
	}

}
