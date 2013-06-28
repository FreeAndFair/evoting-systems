package uk.ac.surrey.pav.bulletinboard.exceptions;

/**
 * This error is thrown when it is found that the database does not contain
 * all the required information or where this is not correct
 * 
 * @author David Lundin
 *
 */
public class DatabaseInsaneException extends LoggedException {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	
	/**
	 * Default constructor
	 *
	 */
	public DatabaseInsaneException() {
		
	}
	
	/**
	 * Default constructor
	 * 
	 * @param s A message
	 */
	public DatabaseInsaneException(String s) {
		super(s);
	}

}
