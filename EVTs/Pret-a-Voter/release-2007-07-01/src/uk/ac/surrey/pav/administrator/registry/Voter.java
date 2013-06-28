package uk.ac.surrey.pav.administrator.registry;

import java.io.Serializable;
import java.sql.Date;
import java.util.ArrayList;

import javax.swing.table.DefaultTableModel;

/**
 * The voter we are currently administrating
 * 
 * @author David Lundin
 *
 */
public class Voter implements Serializable {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * The voter's University Registration Number
	 */
	public String urn;
	
	/**
	 * The voter's primary key in the database
	 */
	public int databaseID;
	
	/**
	 * The voter's name
	 */
	public String name;
	
	/**
	 * Voter's date of birth
	 */
	public Date dob;
	
	/**
	 * A list of all the ballot forms assigned to this person
	 */
	public ArrayList ballotForms = new ArrayList();
	
	/**
	 * Constructor
	 * 
	 * @param databaseID
	 * @param urn
	 * @param name
	 * @param dob
	 */
	public Voter(int databaseID, String urn, String name, Date dob) {
		
		//Store these variables
		this.databaseID = databaseID;
		this.urn = urn;
		this.name = name;
		this.dob = dob;
		
	}
	
	/**
	 * Stores a ballot form in the list
	 * 
	 * @param ballotForm
	 */
	public void addBallotForm(VoterBallotFormPaper ballotForm) {
		this.ballotForms.add(ballotForm);
	}
	
	/**
	 * Get a table model to set out the ballots this voter has been assigned
	 * @return A DefaultTableModel of the voter
	 */
	public DefaultTableModel getBallotFormList() {
		
		//Column headers
		Object headers[] = new Object[4];
		headers[0] = "Serial number";
		headers[1] = "Status";
		headers[2] = "Assigned";
		headers[3] = "Current";
		
		//Data
		Object data[][] = new Object[this.ballotForms.size()][4];

		//About the server
		for(int x = 0; x < this.ballotForms.size(); x++) {
			
			data[x][0] = "" + ((VoterBallotFormPaper)this.ballotForms.get(x)).serialNo;
			data[x][1] = "" + ((VoterBallotFormPaper)this.ballotForms.get(x)).status;
			data[x][2] = "" + ((VoterBallotFormPaper)this.ballotForms.get(x)).assigned;
			if(((VoterBallotFormPaper)this.ballotForms.get(x)).current == true) {
				data[x][3] = "ASSIGNED"; 
			} else {
				data[x][3] = "NOT ASSIGNED";
			}

		}
		
		return (new DefaultTableModel(data, headers));

	}
	
	public boolean mayBeAssignedBallotForm() {
		
		boolean mayBe = true;
		for(int x = 0; x < this.ballotForms.size(); x++) {
			if(((VoterBallotFormPaper)this.ballotForms.get(x)).current) {
				mayBe = false;
			}
		}
		return mayBe;
		
	}

}
