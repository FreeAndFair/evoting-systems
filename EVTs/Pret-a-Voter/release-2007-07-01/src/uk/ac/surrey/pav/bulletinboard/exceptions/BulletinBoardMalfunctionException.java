package uk.ac.surrey.pav.bulletinboard.exceptions;

/**
 * This is thrown when the bulletin board server encounters a
 * problem in an RMI method that is not the caller's fault.
 * 
 * @author David Lundin
 *
 */
public class BulletinBoardMalfunctionException extends LoggedException {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	
	/**
	 * Default constructor
	 *
	 */
	public BulletinBoardMalfunctionException() {
		
	}
	
	/**
	 * Default constructor
	 * 
	 * @param s A message
	 */
	public BulletinBoardMalfunctionException(Exception e, String s) {
		super();
	}
	
}
