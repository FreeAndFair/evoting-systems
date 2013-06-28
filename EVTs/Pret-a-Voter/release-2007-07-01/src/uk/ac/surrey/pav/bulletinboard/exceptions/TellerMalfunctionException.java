package uk.ac.surrey.pav.bulletinboard.exceptions;

/**
 * This is thrown when a query to a teller returns unusable data
 * 
 * @author David Lundin
 *
 */
public class TellerMalfunctionException extends LoggedException {
	
	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	
	/**
	 * Default constructor
	 *
	 */
	public TellerMalfunctionException() {
		
	}
	
	/**
	 * Default constructor
	 * 
	 * @param s A message
	 */
	public TellerMalfunctionException(String s) {
		super(s);
	}

}
