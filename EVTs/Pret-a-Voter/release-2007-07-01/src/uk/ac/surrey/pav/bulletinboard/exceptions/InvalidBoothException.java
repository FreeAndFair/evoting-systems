package uk.ac.surrey.pav.bulletinboard.exceptions;

/**
 * This is thrown by the bulletin board if a booth is submitting
 * but its ID cannot be found or its signature is invalid
 * 
 * @author David Lundin
 *
 */
public class InvalidBoothException extends LoggedException {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	
	/**
	 * Default constructor
	 *
	 */
	public InvalidBoothException() {
		
	}
	
	/**
	 * Default constructor
	 * 
	 * @param s A message
	 */
	public InvalidBoothException(String s) {
		super(s);
	}

}
