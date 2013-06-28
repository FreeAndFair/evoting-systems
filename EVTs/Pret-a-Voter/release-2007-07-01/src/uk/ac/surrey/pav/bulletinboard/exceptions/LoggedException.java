package uk.ac.surrey.pav.bulletinboard.exceptions;

/**
 * This logs the error with corresponding information
 * 
 * @author David Lundin
 *
 */
public class LoggedException extends Exception {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	
	/**
	 * Default constructor
	 *
	 */
	public LoggedException() {
		
	}
	
	/**
	 * Default constructor
	 * 
	 * @param s A message
	 */
	public LoggedException(String s) {
		super(s);
	}
	
	public LoggedException(Exception e, String s) {
		super(s, e);
	}

}
