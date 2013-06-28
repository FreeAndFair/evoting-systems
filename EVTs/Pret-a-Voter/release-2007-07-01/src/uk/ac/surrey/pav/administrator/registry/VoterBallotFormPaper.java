package uk.ac.surrey.pav.administrator.registry;

import java.io.Serializable;
import java.sql.Timestamp;

/**
 * Holds information about a ballot form assigned to a voter
 * 
 * @author David Lundin
 *
 */
public class VoterBallotFormPaper implements Serializable {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * The serial number of the ballot form paper given to this voter
	 */
	public int serialNo;
	
	/**
	 * The string representing the status of this assigned form
	 */
	public String status;
	
	/**
	 * The date and time the form was assigned
	 */
	public Timestamp assigned;
	
	/**
	 * Whether this is a currently assigned ballot or not
	 */
	public boolean current;
	
	
	/**
	 * Constructor
	 * 
	 * @param serialNo
	 * @param status
	 * @param assigned
	 */
	public VoterBallotFormPaper(int serialNo, String status, Timestamp assigned, boolean current) {
		//Simply save the stuff
		this.serialNo = serialNo;
		this.status = status;
		this.assigned = assigned;
		this.current = current;
	}
	
}
