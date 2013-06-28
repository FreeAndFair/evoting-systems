package uk.ac.surrey.pav.bulletinboard.exceptions;

/**
 * This is thrown when the bulletin board notices that a booth
 * is attempting to cast a vote in an election that is currently closed.
 * 
 * @author David Lundin
 *
 */
public class InvalidElectionException extends LoggedException {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	
	/**
	 * Default constructor
	 *
	 */
	public InvalidElectionException() {
		
	}
	
	/**
	 * Default constructor
	 * 
	 * @param s A message
	 */
	public InvalidElectionException(String s) {
		super(s);
	}

}
