package uk.ac.surrey.pav.bulletinboard;

import java.io.BufferedInputStream;
import java.io.ObjectInputStream;
import java.security.PublicKey;
import java.sql.Connection;
import java.sql.DatabaseMetaData;
import java.sql.DriverManager;
import java.sql.ResultSet;
import java.sql.Statement;

import javax.swing.JButton;
import javax.swing.JDialog;
import javax.swing.JLabel;

import uk.ac.surrey.pav.bulletinboard.challenges.Challenge;
import uk.ac.surrey.pav.bulletinboard.entities.AuditMachine;
import uk.ac.surrey.pav.bulletinboard.entities.Batch;
import uk.ac.surrey.pav.bulletinboard.entities.Booth;
import uk.ac.surrey.pav.bulletinboard.entities.Candidate;
import uk.ac.surrey.pav.bulletinboard.entities.Election;
import uk.ac.surrey.pav.bulletinboard.entities.Race;
import uk.ac.surrey.pav.bulletinboard.entities.Teller;
import uk.ac.surrey.pav.bulletinboard.exceptions.DatabaseInsaneException;

/**
 * A thread that makes a connection to the specified database and
 * then loads all required information from it
 * 
 * @author David Lundin
 *
 */
public class DatabaseConnectorThread extends Thread {

	/**
	 * A bulletin board that is returned to the caller
	 */
	private BulletinBoard bulletinBoard;
	
	/**
	 * The url to the database server
	 */
	private String url;
	
	/**
	 * User name to pass to the database server
	 */
	private String userName;
	
	/**
	 * Password to database
	 */
	private String password;
	
	/**
	 * JLabel object that is used to output the current state of the database connection
	 */
	private JLabel statusLabel;
	
	/**
	 * Button that closes the window
	 */
	private JButton okButton;
	
	/**
	 * The window
	 */
	private JDialog dialog;
	
	/**
	 * Whether or not everything has been loaded properly: set to false
	 * when something goes wrong
	 */
	private boolean allIsWell = true;
	
	/**
	 * This thread connects to the database and loads all the necessary entities from it.
	 * It constructs a bulletin board object and returns this as well as an open
	 * database connection.
	 * 
	 * @param connection
	 * @param bulletinBoard
	 * @param url
	 * @param userName
	 * @param password
	 * @param statusLabel
	 * @param okButton
	 * @param dialog
	 */
	DatabaseConnectorThread(BulletinBoard bulletinBoard, String url, String userName, String password, JLabel statusLabel, JButton okButton, JDialog dialog) {
		
		//Store values of connection variables
		this.bulletinBoard = bulletinBoard;
		this.url = url;
		this.userName = userName;
		this.password = password;
		
		//Store reference to the JLabel used to output current status etc
		this.statusLabel = statusLabel;
		this.okButton = okButton;
		this.dialog = dialog;
		
	}
	
	/**
	 * Used to output the status to the user window
	 *  
	 * @param status A string describing the current status of the connection
	 */
	private void setStatus(String status) {
		
		//System out
		System.out.println(status);
		
		//Set the JLabel to the current status
		this.statusLabel.setText(status);
		
	}
	
	/**
	 * Ends the transaction by enabling the OK button etc
	 *
	 */
	private void finish() {
		
		//Set the OK button to be enabled
		this.okButton.setEnabled(true);
		
		//If everything went well, dispose of window
		if(this.allIsWell) {
			//Hide the window etc
			dialog.setVisible(false);
		}
		
	}
	
	/**
	 * What this thread actually does
	 */
	public void run() {
		
		setStatus("Attempting to connect to database...");
		
		try {

			/*
			 * CREATE THE CONNECTION TO THE DATABASE
			 * 
			 */
			
			//Load the database connection driver
			Class.forName ("com.mysql.jdbc.Driver");

			//Make the connection
			Connection connection = DriverManager.getConnection(this.url, this.userName, this.password);
			
			//Meta data about the database
			DatabaseMetaData dma = connection.getMetaData();

			//Report being connected
			setStatus("Connected to " + dma.getURL());
	
			//Pass the connection back to caller
			this.bulletinBoard.setConnection(connection);
			
			/*
			 * LOAD ELECTION INFORMATION FROM THE DATABASE
			 * 
			 */
			
			//Create a statement
			Statement statement = connection.createStatement(ResultSet.TYPE_SCROLL_INSENSITIVE, ResultSet.CONCUR_READ_ONLY);

			/*
			 * LOAD ELECTIONS
			 */
			
			setStatus("Loading elections...");

			//Count the number of elections
			int electionCount = 0;
			
			//Select all tellers
			ResultSet rsElections = statement.executeQuery("SELECT * FROM elections");
			
			//Iterate through all loaded elections
			while(rsElections.next()) {

				setStatus("Loaded election: " + rsElections.getString("election_name"));
				
				//Count the number of ballots cast in this election
				int ballotCount = 0;
				Statement countStatement = connection.createStatement(ResultSet.TYPE_SCROLL_INSENSITIVE, ResultSet.CONCUR_READ_ONLY);
				ResultSet rsCount = countStatement.executeQuery("SELECT COUNT(*) AS ballots FROM ballotforms WHERE ballotform_status = 'VOTED' AND election_id = " + rsElections.getInt("election_id"));
				if(rsCount.next()) {
					ballotCount = rsCount.getInt("ballots");
				}
				int ballotAuditedCount = 0;
				rsCount = countStatement.executeQuery("SELECT COUNT(*) AS ballots FROM ballotforms WHERE ballotform_status = 'AUDITED' AND election_id = " + rsElections.getInt("election_id"));
				if(rsCount.next()) {
					ballotAuditedCount = rsCount.getInt("ballots");
				}

				//Create new election element and store this
				Election newElection = new Election(ballotCount, ballotAuditedCount, rsElections.getInt("election_id"), rsElections.getString("election_name"), rsElections.getDate("election_startdate"), rsElections.getDate("election_enddate"));
				this.bulletinBoard.addElection(newElection);
				
				/*
				 * Load the races in this election
				 */
				
				//Create a statement
				Statement raceStatement = connection.createStatement(ResultSet.TYPE_SCROLL_INSENSITIVE, ResultSet.CONCUR_READ_ONLY);

				//Load the races
				ResultSet rsRaces = raceStatement.executeQuery("SELECT * FROM races WHERE election_id = " + newElection.electionID + " ORDER BY race_id ASC");
				
				//Count the races
				int raceCount = 0;
				
				//Iterate through all these races
				while(rsRaces.next()) {
				
					setStatus("Loaded race: " + rsRaces.getString("race_name"));
					
					//Count the number of ballots cast in this race
					ballotCount = 0;
					countStatement = connection.createStatement(ResultSet.TYPE_SCROLL_INSENSITIVE, ResultSet.CONCUR_READ_ONLY);
					rsCount = countStatement.executeQuery("SELECT COUNT(*) AS ballots FROM ballotforms WHERE ballotform_status = 'VOTED' AND election_id = " + newElection.electionID + " AND race_id = " + rsRaces.getInt("race_id"));
					if(rsCount.next()) {
						ballotCount = rsCount.getInt("ballots");
					}
					
					//Create new race object and add it to the list
					Race newRace = new Race(ballotCount, newElection, rsRaces.getInt("race_id"), rsRaces.getString("race_name"));
					newElection.addRace(newRace);

					//Load the batches created for this race
					Statement batchStatement = connection.createStatement(ResultSet.TYPE_SCROLL_INSENSITIVE, ResultSet.CONCUR_READ_ONLY);
					ResultSet rsBatches = batchStatement.executeQuery("SELECT teller_id, COUNT(*) AS form_count FROM receipts WHERE election_id = " + newRace.election.electionID + " AND race_id = " + newRace.raceID + " AND teller_batch = 0 GROUP BY teller_id, teller_batch ORDER BY teller_id DESC");
					while(rsBatches.next()) {
						newRace.addBatch(new Batch(rsBatches.getInt("teller_id"), rsBatches.getInt("form_count")));
					}

					//Load the challenges created for this race
					Statement challengeStatement = connection.createStatement(ResultSet.TYPE_SCROLL_INSENSITIVE, ResultSet.CONCUR_READ_ONLY);
					ResultSet rsChallenges = challengeStatement.executeQuery("SELECT * FROM commitments WHERE election_id = " + newRace.election.electionID + " AND race_id = " + newRace.raceID + " ORDER BY teller_id ASC");
					while(rsChallenges.next()) {
						newRace.addChallenge(new Challenge(rsChallenges.getInt("teller_id"), rsChallenges.getBytes("commitment_bulletinboard_nonce"), rsChallenges.getBytes("commitment_commitment"), rsChallenges.getBytes("commitment_teller_nonce"), rsChallenges.getBytes("commitment_bitmap")));
					}

					/*
					 * Load the candidates in this race
					 */
					
					//Create a statement
					Statement candidateStatement = connection.createStatement(ResultSet.TYPE_SCROLL_INSENSITIVE, ResultSet.CONCUR_READ_ONLY);

					//Load the races
					ResultSet rsCandidates = candidateStatement.executeQuery("SELECT c.* FROM candidateraces cr, candidates c WHERE cr.candidate_id = c.candidate_id AND cr.election_id = " + newElection.electionID + " AND race_id = " + newRace.raceID);
					
					//Count the candidates
					int candidateCount = 0;
					
					//Iterate through all the candidates
					while(rsCandidates.next()) {
						
						//Create new candidate element and add it to the list
						Candidate newCandidate = new Candidate(rsCandidates.getInt("candidate_id"), rsCandidates.getString("candidate_name"));
						newRace.addCandidate(newCandidate);

						//System.out.println("Candidate " + newCandidate.name + " in election " + newElection.name + " race " + newRace.name);
						
						//Increment counter
						candidateCount++;
						
					}
					
					setStatus("Loaded " + candidateCount + " candidates for this race");
					
					//Increment counter
					raceCount++;
					
				}
				
				setStatus("Loaded " + raceCount + " races for this election");
				
				//Increase election counter
				electionCount++;
				
			}

			setStatus("Loaded " + electionCount + " elections");

			/*
			 * LOAD TELLERS
			 */
			
			setStatus("Loading tellers...");
			
			//Count the number of tellers
			int tellerCount = 0;
			
			//Select all tellers
			ResultSet rsTellers = statement.executeQuery("SELECT * FROM tellers ORDER BY teller_sequencenumber ASC");
			
			//Iterate through the result set
			while(rsTellers.next()) {
			
				//Deserialise the public key
				ObjectInputStream deserialisedKey = new ObjectInputStream(new BufferedInputStream(rsTellers.getBinaryStream("teller_publickey")));
				
				//Create a teller object and add it to the bulletin board
				this.bulletinBoard.addTeller(new Teller(rsTellers.getInt("teller_id"),
														rsTellers.getString("teller_name"),
														rsTellers.getString("teller_ipaddress"),
														rsTellers.getString("teller_servername"),
														(PublicKey)deserialisedKey.readObject(),
														rsTellers.getInt("teller_sequencenumber")));
				
				//Increase counter
				tellerCount++;
				
			}
			
			setStatus("Loaded " + tellerCount + " tellers");
			
			/*
			 * LOAD BOOTHS
			 */
			
			setStatus("Loading booths...");
			
			//Count the number of booths
			int boothCount = 0;
			
			//Select all booths
			ResultSet rsBooths = statement.executeQuery("SELECT * FROM booths");
			
			//Iterate through all the booths
			while(rsBooths.next()) {

				//Deserialise the public key
				ObjectInputStream deserialisedKey = new ObjectInputStream(new BufferedInputStream(rsBooths.getBinaryStream("booth_publickey")));

				//Count the number of ballots cast from this booth
				int ballotCount = 0;
				Statement countStatement = connection.createStatement(ResultSet.TYPE_SCROLL_INSENSITIVE, ResultSet.CONCUR_READ_ONLY);
				ResultSet rsCount = countStatement.executeQuery("SELECT COUNT(*) AS ballots FROM ballotforms WHERE ballotform_status = 'VOTED' AND booth_id = " + rsBooths.getInt("booth_id"));
				if(rsCount.next()) {
					ballotCount = rsCount.getInt("ballots");
				}

				//Create a new booth object and add it
				this.bulletinBoard.addBooth(new Booth(ballotCount, rsBooths.getInt("booth_id"), rsBooths.getString("booth_name"), (PublicKey)deserialisedKey.readObject()));
				
				//Increase counter
				boothCount++;
				
			}

			setStatus("Loaded " + boothCount + " booths");

			/*
			 * LOAD AUDIT MACHINES
			 */
			
			setStatus("Loading audit machines...");
			
			//Count the number of booths
			int auditMachineCount = 0;
			
			//Select all booths
			ResultSet rsAuditMachines = statement.executeQuery("SELECT * FROM auditmachines");
			
			//Iterate through all the booths
			while(rsAuditMachines.next()) {

				//Deserialise the public key
				ObjectInputStream deserialisedKey = new ObjectInputStream(new BufferedInputStream(rsAuditMachines.getBinaryStream("auditmachine_publickey")));

				//Count the number of ballots audited from this audit machine
				int ballotCount = 0;
				Statement countStatement = connection.createStatement(ResultSet.TYPE_SCROLL_INSENSITIVE, ResultSet.CONCUR_READ_ONLY);
				ResultSet rsCount = countStatement.executeQuery("SELECT COUNT(*) AS ballots FROM ballotforms WHERE ballotform_status = 'AUDITED' AND booth_id = " + rsAuditMachines.getInt("auditmachine_id"));
				if(rsCount.next()) {
					ballotCount = rsCount.getInt("ballots");
				}

				//Create a new booth object and add it
				this.bulletinBoard.addAuditMachine(new AuditMachine(ballotCount, rsAuditMachines.getInt("auditmachine_id"), rsAuditMachines.getString("auditmachine_name"), (PublicKey)deserialisedKey.readObject()));
				
				//Increase counter
				auditMachineCount++;
				
			}

			setStatus("Loaded " + auditMachineCount + " audit machines");

			setStatus("Loading from database complete.");

			/*
			 * SANITY CHECK
			 */
			
			//RULE: There must exist at least one election
			if(electionCount < 1) {
				this.allIsWell = false;
				throw (new DatabaseInsaneException("No election loaded."));
			}
			
			//RULE: There must exist at least two tellers
			if(tellerCount < 2) {
				this.allIsWell = false;
				throw (new DatabaseInsaneException("There must exist at least two tellers."));
			}
			
			//RULE: There must exist at least one booth
			if(boothCount < 1) {
				this.allIsWell = false;
				throw (new DatabaseInsaneException("There must exist at least one booth."));
			}
			
			//WARNING RULE: If there are no audit machines
			if(auditMachineCount < 1) {
				this.allIsWell = false;
				setStatus("WARNING: There exist no audit machines.");
			}
			
			//Finish up
			finish();
			
		} catch (Exception e) {

			//It's not all well.
			this.allIsWell = false;

			//There was an exception, display and end
			setStatus(e.toString());
			e.printStackTrace();
			
			//There is now no connection
			this.bulletinBoard.setConnection(null);
			
			//Finish up
			finish();
			
		}
	}
}
