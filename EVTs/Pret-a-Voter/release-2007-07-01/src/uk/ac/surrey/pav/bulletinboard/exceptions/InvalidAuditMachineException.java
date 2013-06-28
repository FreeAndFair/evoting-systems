package uk.ac.surrey.pav.bulletinboard.exceptions;

/**
 * Thrown when the audit machine does not exist or the signature
 * is invalid
 * 
 * @author David Lundin
 *
 */
public class InvalidAuditMachineException extends LoggedException {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	
	/**
	 * Default constructor
	 *
	 */
	public InvalidAuditMachineException() {
		
	}
	
	/**
	 * Default constructor
	 * 
	 * @param s A message
	 */
	public InvalidAuditMachineException(String s) {
		super(s);
	}

}
