package uk.ac.surrey.pav.bulletinboard.exceptions;

/**
 * This is thrown when the bulletin board is trying to access a
 * teller but this results in a RemoteException
 * 
 * @author David Lundin
 *
 */
public class TellerDownException extends LoggedException {
	
	//The ID of the teller that is down
	public int tellerID;

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	
	/**
	 * Default constructor
	 *
	 */
	public TellerDownException(int tellerID) {
		this.tellerID = tellerID;
	}
	
	/**
	 * Default constructor
	 * 
	 * @param s A message
	 */
	public TellerDownException(String s, int tellerID) {
		super(s);
		this.tellerID = tellerID;
	}
	
}
