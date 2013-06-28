package uk.ac.surrey.pav.audit;

import java.util.Date;

/**
 * During the audit, this represents a logged event
 * 
 * @author David Lundin
 *
 */
public class AuditTableRow {

	/**
	 * Timestamp for the row
	 */
	public Date timeStamp = new Date();
	
	/**
	 * Action
	 */
	public String action;
	
	/**
	 * Result
	 */
	public String result;
	
	/**
	 * Constructor
	 * 
	 * @param action
	 * @param result
	 */
	public AuditTableRow(String action, String result) {
		this.action = action;
		this.result = result;
	}
	
	public String getCol(int x) {
		if(x == 0) {
			return this.timeStamp.toString();
		} else if(x == 1) {
			return this.action;
		} else {
			return this.result;
		}
	}
	
}
