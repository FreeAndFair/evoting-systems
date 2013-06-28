package uk.ac.surrey.pav.bulletinboard;

import java.security.PrivateKey;
import java.security.PublicKey;
import java.sql.Connection;
import java.util.ArrayList;

import uk.ac.surrey.pav.bulletinboard.entities.AuditMachine;
import uk.ac.surrey.pav.bulletinboard.entities.Booth;
import uk.ac.surrey.pav.bulletinboard.entities.Election;
import uk.ac.surrey.pav.bulletinboard.entities.Teller;

/**
 * Stores all data that the bulletin board needs to know, for example
 * about all the tellers, booths etc
 * 
 * @author David Lundin
 *
 */
public class BulletinBoard {

	/**
	 * The private key of the bulletin board
	 */
	public PrivateKey privateKey;
	
	/**
	 * The public key of the administrator
	 */
	public PublicKey administratorPublicKey;

	/**
	 * A list of all the current elections.
	 */
	private ArrayList elections = new ArrayList();
	
	/**
	 * Stores the list of tellers that the bulletin board
	 * knows about.
	 */
	private ArrayList tellers = new ArrayList();
	
	/**
	 * Stores the list of voting booths that the bulletin board
	 * knows about.
	 */
	private ArrayList booths = new ArrayList();
	
	/**
	 * Stores the list of audit machines that the bulletin board
	 * knows about.
	 */
	private ArrayList auditMachines = new ArrayList();
	
	/**
	 * Connection to the database
	 */
	public Connection connection;
	
	/**
	 * Constructor
	 * 
	 * @param privateKey A private key for the bulletin board to use
	 */
	public BulletinBoard(PrivateKey privateKey, PublicKey administratorPublicKey) {
		//Store the private key and the administrator's public key
		this.privateKey = privateKey;
		this.administratorPublicKey = administratorPublicKey;
	}
	
	/**
	 * Test if enough data has been collected to start the
	 * election;
	 * 
	 * @return	Boolean representing whether or not the election is ready to be run
	 */
	public boolean testStartElection() {
		//Test if I have a private key
		if(this.privateKey == null) {
			System.out.println("ERROR! No private key for the bulletin board specified.");
			return false;
		}
		
		//Test if I have at least two tellers
		if(this.tellers.size() < 2) {
			System.out.println("ERROR! Only " + this.tellers.size() + " tellers specified, minimum 2!");
			return false;
		}
		
		//Test if I have at least one booth
		if(this.booths.size() < 1) {
			System.out.println("ERROR! No voting booths specified!");
			return false;
		}
		
		//Warn if no audit machines
		if(this.auditMachines.size() < 1) System.out.println("WARNING! No audit machines registered.");
		
		//Rock and roll
		return true;
	}
	
	/**
	 * Stores a database connection
	 * 
	 * @param connection
	 */
	public void setConnection(Connection connection) {
		this.connection = connection;
	}
	
	/**
	 * Tests if there is presently a database connection referenced from this bulletin board
	 * 
	 * @return Boolean representing the existance of a database connection
	 */
	public boolean testConnection() {
		if(this.connection != null) {
			return true;
		} else {
			return false;
		}
	}
	
	/**
	 * Add a teller to the list
	 * 
	 * @param teller A complete teller object
	 */
	public void addTeller(Teller teller) {
		//Add it to the list
		this.tellers.add(teller);
	}
	
	/**
	 * Add a booth to the list
	 * 
	 * @param booth A complete Booth object
	 */
	public void addBooth(Booth booth) {
		//Add booth to the list
		this.booths.add(booth);
	}

	/**
	 * Add an election to the list
	 * 
	 * @param election A complete Election object 
	 */
	public void addElection(Election election) {
		//Add election to list
		this.elections.add(election);
	}
	
	/**
	 * Adds an audit machine to the list
	 * 
	 * @param auditMachine A complete AuditMachine object
	 */
	public void addAuditMachine(AuditMachine auditMachine) {
		//Add to list
		this.auditMachines.add(auditMachine);
	}
	
	/*
	 * Creates a list of all the elections and returns a DefaultTableModel
	 * that can be added to a JTable to display it.
	 * 
	 * @return DefaultTableModel
	 */
	/*public DefaultTableModel getElectionList() {

		//Column headers
		Object headers[] = new Object[6];
		headers[0] = "ID";
		headers[1] = "Name";
		headers[2] = "Start date";
		headers[3] = "End date";
		headers[4] = "Ballots cast";
		headers[5] = "Ballots audited";
		
		//Data
		Object data[][] = new Object[this.elections.size()][6];
		
		//Go through all elections and add to data
		for(int y=0; y<this.elections.size(); y++) {
			//Add all columns
			data[y][0] = "" + ((Election)this.elections.get(y)).electionID;
			data[y][1] = ((Election)this.elections.get(y)).name;
			data[y][2] = ((Election)this.elections.get(y)).startDate;
			data[y][3] = ((Election)this.elections.get(y)).endDate;
			data[y][4] = "" + ((Election)this.elections.get(y)).ballotCount;
			data[y][5] = "" + ((Election)this.elections.get(y)).ballotAuditCount;
		}
		
		return (new DefaultTableModel(data, headers));
		
	}*/

	/*
	 * Creates a list of all the tellers and returns a DefaultTableModel
	 * that can be added to a JTable to display it.
	 * 
	 * @return DefaultTableModel
	 */
	/*public DefaultTableModel getTellerList() {
		//Column headers
		Object headers[] = new Object[8];
		headers[0] = "ID";
		headers[1] = "Name";
		headers[2] = "IP Address";
		headers[3] = "Server name";
		headers[4] = "Sequence no";
		headers[5] = "Public key";
		headers[6] = "Connection";
		headers[7] = "Conn-err";
		
		//Data
		Object data[][] = new Object[this.tellers.size()][8];
		
		//Go through all rows and add to data
		for(int y=0; y<this.tellers.size(); y++) {
			//Add all columns
			data[y][0] = "" + ((Teller)this.tellers.get(y)).tellerID;
			data[y][1] = ((Teller)this.tellers.get(y)).name;
			data[y][2] = ((Teller)this.tellers.get(y)).address;
			data[y][3] = ((Teller)this.tellers.get(y)).serverName;
			data[y][4] = "" + ((Teller)this.tellers.get(y)).sequenceNumber;
			data[y][5] = ((Teller)this.tellers.get(y)).publicKey.toString();
			data[y][6] = ((Teller)this.tellers.get(y)).connectionState;
			data[y][7] = "" + ((Teller)this.tellers.get(y)).connectionErrorCount;
		}
		
		return (new DefaultTableModel(data, headers));
		
	}*/

	/*
	 * Creates a list of all the voting booths and returns a DefaultTableModel
	 * that can be added to a JTable to display it.
	 * 
	 * @return DefaultTableModel
	 */
	/*public DefaultTableModel getBoothList() {
		//Column headers
		Object headers[] = new Object[4];
		headers[0] = "ID";
		headers[1] = "name";
		headers[2] = "Public key";
		headers[3] = "Ballots cast";
		
		//Data
		Object data[][] = new Object[this.booths.size()][4];
		
		//Go through all rows and add to data
		for(int y=0; y<this.booths.size(); y++) {
			//Add all columns
			data[y][0] = "" + ((Booth)this.booths.get(y)).boothID;
			data[y][1] = ((Booth)this.booths.get(y)).name;
			data[y][2] = ((Booth)this.booths.get(y)).publicKey.toString();
			data[y][3] = "" + ((Booth)this.booths.get(y)).ballotCount;
		}
		
		return (new DefaultTableModel(data, headers));
		
	}*/

	/*
	 * Creates a list of all the audit machines and returns a DefaultTableModel
	 * that can be added to a JTable to display it.
	 * 
	 * @return DefaultTableModel
	 */
	/*public DefaultTableModel getAuditMachineList() {
		//Column headers
		Object headers[] = new Object[4];
		headers[0] = "ID";
		headers[1] = "name";
		headers[2] = "Public key";
		headers[3] = "Forms audited";
		
		//Data
		Object data[][] = new Object[this.auditMachines.size()][4];
		
		//Go through all rows and add to data
		for(int y=0; y<this.auditMachines.size(); y++) {
			//Add all columns
			data[y][0] = "" + ((AuditMachine)this.auditMachines.get(y)).auditMachineID;
			data[y][1] = ((AuditMachine)this.auditMachines.get(y)).name;
			data[y][2] = ((AuditMachine)this.auditMachines.get(y)).publicKey.toString();
			data[y][3] = "" + ((AuditMachine)this.auditMachines.get(y)).ballotCount;
		}
		
		return (new DefaultTableModel(data, headers));
		
	}*/

	/**
	 * Stores the private key that has been loaded for the Web Bulletin Board module
	 * 
	 * @param privateKey A PrivateKey element
	 */
	public void setPrivateKey(PrivateKey privateKey) {
		//Store the public key
		this.privateKey = privateKey;
	}
	
	/**
	 * Count the number of tellers
	 * 
	 * @return The number of tellers
	 */
	public int getTellerCount() {
		return this.tellers.size();
	}
	
	/**
	 * Returns a teller
	 * 
	 * @param x	The index of the teller
	 * @return	Teller object
	 */
	public Teller getTeller(int x) {
		if(x >= 0 && x <= this.tellers.size()) {
			return (Teller)this.tellers.get(x);
		} else {
			return null;
		}
	}
	
	/**
	 * Count the number of booths
	 * 
	 * @return The number of booths
	 */
	public int getBoothCount() {
		return this.booths.size();
	}
	
	/**
	 * Finds a booth from an ID number
	 * 
	 * @param boothID The ID of the booth, primary key in database
	 * @return Booth or null
	 */
	public Booth getBoothFromID(int boothID) {
		//Go through all booths
		Booth foundBooth = null;
		for(int x=0; x<this.booths.size(); x++) {
			if(((Booth)this.booths.get(x)).boothID == boothID) {
				foundBooth = (Booth)this.booths.get(x);
			}
		}
		return foundBooth;
	}

	/**
	 * Finds an audit machine from an ID number
	 * 
	 * @param auditMachineID	The ID number of the audit machine, primary key in the database
	 * @return					AuditMachine object or null
	 */
	public AuditMachine getAuditMachineFromID(int auditMachineID) {
		//Go through all booths
		AuditMachine foundAuditMachine = null;
		for(int x=0; x<this.auditMachines.size(); x++) {
			if(((AuditMachine)this.auditMachines.get(x)).auditMachineID == auditMachineID) {
				foundAuditMachine = (AuditMachine)this.auditMachines.get(x);
			}
		}
		return foundAuditMachine;
	}
	
	/**
	 * Finds an election from an election ID
	 * 
	 * @param electionID	The ID of the election sought
	 * @return				Election object
	 */
	public Election getElectionFromID(int electionID) {
		//Go through all elections
		Election foundElection = null;
		for(int x=0; x<this.elections.size(); x++) {
			if(((Election)this.elections.get(x)).electionID == electionID) {
				foundElection = (Election)this.elections.get(x);
			}
		}
		return foundElection;
	}
	
	/**
	 * Returns the number of elections
	 * 
	 * @return Number of elections
	 */
	public int getElectionCount() {
		return this.elections.size();
	}
	
	/**
	 * Returns an array of all the elections
	 * 
	 * @return Array with all the elections
	 */
	public Election[] getElectionArray() {
		//Result array
		Election[] result = new Election[this.elections.size()];
		
		//Populate result array
		for(int x=0; x<this.elections.size(); x++) {
			result[x] = (Election)this.elections.get(x);
		}
		
		//Return result array
		return result;
	}
	
	/**
	 * Returns an array of all the tellers
	 * 
	 * @return An array of tellers
	 */
	public Teller[] getTellerArray() {
		//Result array
		Teller[] result = new Teller[this.tellers.size()];
		
		//Populate result array
		for(int x=0; x<this.tellers.size(); x++) {
			result[x] = (Teller)this.tellers.get(x);
		}
		
		//Return result array
		return result;
	}

	/**
	 * Returns an array of the booths
	 * 
	 * @return An array of the booths
	 */
	public Booth[] getBoothArray() {
		//Result array
		Booth[] result = new Booth[this.booths.size()];
		
		//Populate result array
		for(int x=0; x<this.booths.size(); x++) {
			result[x] = (Booth)this.booths.get(x);
		}
		
		//Return result array
		return result;
	}
	
	/**
	 * Returns an array of the audit machines
	 * 
	 * @return Array of AuditMachine
	 */
	public AuditMachine[] getAuditMachineArray() {
		//Result array
		AuditMachine[] result = new AuditMachine[this.auditMachines.size()];
		
		//Populate result array
		for(int x=0; x<this.auditMachines.size(); x++) {
			result[x] = (AuditMachine)this.auditMachines.get(x);
		}
		
		//Return result array
		return result;
	}
	
	/**
	 * Returns the first teller found with a specified teller name
	 * 
	 * @param tellerName The name of the teller sought
	 * @return The teller if found
	 */
	public Teller getTellerByName(String tellerName) {
		
		//Search for a teller with this name
		for(int x = 0; x < this.tellers.size(); x++) {
			
			//Check this teller
			Teller currentTeller = (Teller)this.tellers.get(x);
			if(currentTeller.name.matches(tellerName)) {
				
				//We have found a match so return it
				return currentTeller;
				
			}
		}
		
		//No teller was found so return nothing
		return null;
	}

}
