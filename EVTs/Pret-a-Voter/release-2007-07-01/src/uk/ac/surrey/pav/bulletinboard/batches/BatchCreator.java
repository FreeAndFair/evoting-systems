package uk.ac.surrey.pav.bulletinboard.batches;

import java.io.BufferedInputStream;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;
import java.util.ArrayList;

import uk.ac.surrey.pav.ballotform.BallotForm;
import uk.ac.surrey.pav.ballotform.PartialForm;
import uk.ac.surrey.pav.ballotform.TellerBatch;
import uk.ac.surrey.pav.bulletinboard.entities.Batch;
import uk.ac.surrey.pav.bulletinboard.entities.Race;
import uk.ac.surrey.pav.bulletinboard.entities.Teller;
import uk.ac.surrey.pav.bulletinboard.exceptions.DatabaseInsaneException;
import uk.ac.surrey.pav.bulletinboard.exceptions.TellerMalfunctionException;

/**
 * Stores information about the process of creating a batch
 * as well as instantiates threads to do the work.
 * 
 * @author David Lundin
 *
 */
public class BatchCreator implements Runnable {
	
	/**
	 * The race for which a TellerBatch object is created
	 */
	private Race race;
	
	/**
	 * Database connection to use
	 */
	private Connection connection;
	
	/**
	 * Count of the ballot forms processed
	 */
	private int ballotCount = 0;
	
	/**
	 * Number of ballot forms to go through
	 */
	private int totalBallotCount = 0;
	
	/**
	 * The result of this thread's labours
	 */
	private TellerBatch resultBatch;
	
	/**
	 * What I am currently doing in human readable form
	 */
	private String currentAction;
	
	/**
	 * Whether or not I am currently working
	 */
	private boolean isWorking = true;
	
	/**
	 * List of the tellers to send the receipts through
	 */
	private Teller[] tellers;
	
	/**
	 * Constructor when the thread is used to create the initial batch
	 * 
	 * @param race
	 */
	public BatchCreator(Connection connection, Race race, Teller[] tellers) {
		
		//Store the references
		this.connection = connection;
		this.race = race;
		this.tellers = tellers;
		
	}
	
	private TellerBatch loadInitialBatch() throws IOException, SQLException, ClassNotFoundException {
		
		/*
		 * Get ballot forms from database
		 */
		
		//Say what I am doing
		this.currentAction = "Creating initial batch...";
		
		//Create a statement
		Statement statement = connection.createStatement(ResultSet.TYPE_SCROLL_INSENSITIVE, ResultSet.CONCUR_READ_ONLY);
		
		//Select all ballotforms
		ResultSet rsBallotForms = statement.executeQuery("SELECT * FROM ballotforms WHERE election_id = " + this.race.election.electionID + " AND race_id = " + this.race.raceID + " AND ballotform_status = 'VOTED'");
		
		//Create a TellerBatch object
		resultBatch = new TellerBatch();
		
		//The number of ballot forms to add to batch
		rsBallotForms.last();
		this.totalBallotCount = rsBallotForms.getRow();
		this.ballotCount = 0;
		rsBallotForms.beforeFirst();
		System.out.println("Ballot forms to process: " + this.totalBallotCount);
		
		//Iterate through all ballotforms
		while(rsBallotForms.next()) {
			
			//Deserialise the ballot form
			ObjectInputStream deserialisedBallotForm = new ObjectInputStream(new BufferedInputStream(rsBallotForms.getBinaryStream("ballotform_object")));
			BallotForm currentBallotForm = (BallotForm)deserialisedBallotForm.readObject();
			
			//Create PartialForm object
			PartialForm partialForm = new PartialForm(currentBallotForm.votingForm.signedOnion.onion, currentBallotForm.votingForm.vote);
			
			//Add this PartialForm to the batch
			resultBatch.addBallotForm(partialForm);
			
			//Increment counter
			this.ballotCount++;
			
		}
		
		System.out.println("Included " + ballotCount + " ballot forms in the batch.");
		
		//Return the batch
		return resultBatch;
		
	}
	
	/**
	 * Returns an integer representing the percentage done
	 * 
	 * @return Integer between 0 and 100
	 */
	public int getPercentageDone() {
		if(this.totalBallotCount > 0) {
			return (int)(((double)this.ballotCount / (double)this.totalBallotCount) * 100);
		} else {
			return 0;
		}
	}
	
	/**
	 * What I am doing as a thread
	 */
	public void run() {
		
		try {
			
			//I am working now
			this.isWorking = true;
			
			//The batch I am currently working with
			TellerBatch currentBatch;

			//Do not auto commit
			this.connection.setAutoCommit(false);

			//Check if there are any batches
			if(this.race.getNumberOfBatches() == 0) {
				//There are no batches
				
				//Create the initial batch for this race
				currentBatch = this.loadInitialBatch();
				
			} else {
				//There are batches

				//so load the most recent from the database
				currentBatch = this.loadBatchFromDatabase();
				
			}
			
			//Make sure there is at least one ballot form in the batch
			if(currentBatch.ballotForms.size() <= 0) {
				throw new DatabaseInsaneException("No ballot forms could be loaded from the database into the batch.");
			}

			//While there is more to do, keep going
			while(this.race.getNumberOfBatches() < this.tellers.length) {
				
				//Determine which is the current teller
				int currentTellerOrderNumber = this.tellers.length - this.race.getNumberOfBatches() - 1;

				//Pass this batch to the next teller
				this.currentAction = "Sending batch to Teller " + this.tellers[currentTellerOrderNumber].name;
				//TODO: The batch ID here is always set to 0 because we always send exactly one batch for each race
				ArrayList twoBatches = this.tellers[currentTellerOrderNumber].processVote(this.race.election.electionID, this.race.raceID, 0, currentBatch);
				
				//Check that something was actually returned
				if(twoBatches == null) {
					throw new TellerMalfunctionException("The teller did not return anything.");
				}

				//Check that there are two batches
				if(twoBatches.size() != 2) {
					throw new TellerMalfunctionException("The teller did not return two batches but rather " + twoBatches.size() + " batches.");
				}
				
				//Devide into two batches
				TellerBatch leftBatch = (TellerBatch)twoBatches.get(0);
				TellerBatch rightBatch = (TellerBatch)twoBatches.get(1);
				
				//These batches better contain the same number of forms!
				if(leftBatch.ballotForms.size() != rightBatch.ballotForms.size()) {
					throw new TellerMalfunctionException("The batches returned by the teller were not the same length.");
				}
				
				/*
				 * Store the resulting batches in the database as a DB BATCH JOB
				 */
				this.currentAction = "Storing batches received from " + this.tellers[currentTellerOrderNumber].name + " in database.";
				
				//An insert statement
				PreparedStatement statement = this.connection.prepareStatement("INSERT INTO receipts (election_id, race_id, teller_id, teller_batch, receipt_partialform, receipt_plaintext_vote) VALUES (?, ?, ?, ?, ?, ?)");
				
				//Add the left batch to the database batch
				for(int x=0; x<leftBatch.ballotForms.size(); x++) {
					
					//Current partial form
					PartialForm currentPartialForm = (PartialForm)leftBatch.ballotForms.get(x);
					
					//Serialise the partial form
					ByteArrayOutputStream baos = new ByteArrayOutputStream();
				    ObjectOutputStream oout = new ObjectOutputStream(baos);
				    oout.writeObject(currentPartialForm);
				    oout.close();
					
					//Add election_id, race_id, teller_id, teller_batch, receipt_partialform
				    statement.setInt(1, this.race.election.electionID);
				    statement.setInt(2, this.race.raceID);
				    statement.setInt(3, currentTellerOrderNumber);
				    statement.setInt(4, 0);
				    statement.setBytes(5, baos.toByteArray());
				    statement.setString(6, currentPartialForm.permutation.toString());
				    
					statement.addBatch();
					
				}
				
				//Add the right batch to the database batch
				for(int x=0; x<rightBatch.ballotForms.size(); x++) {
					
					//Current partial form
					PartialForm currentPartialForm = (PartialForm)rightBatch.ballotForms.get(x); 
					
					//Serialise the partial form
					ByteArrayOutputStream baos = new ByteArrayOutputStream();
				    ObjectOutputStream oout = new ObjectOutputStream(baos);
				    oout.writeObject(currentPartialForm);
				    oout.close();
					
					//Add election_id, race_id, teller_id, teller_batch, receipt_partialform
				    statement.setInt(1, this.race.election.electionID);
				    statement.setInt(2, this.race.raceID);
				    statement.setInt(3, currentTellerOrderNumber);
				    statement.setInt(4, 1);
				    statement.setBytes(5, baos.toByteArray());
				    statement.setString(6, currentPartialForm.permutation.toString());

				    statement.addBatch();
					
				}
				
				//Add batch object to the race object
				Batch newBatch = new Batch(currentTellerOrderNumber, leftBatch.ballotForms.size());
				this.race.addBatch(newBatch);
				
				//Execute the batch
				statement.executeBatch();
				
				//Commit the insert statement
				this.connection.commit();
				
				//The next batch to work on is the final batch from the teller
				currentBatch = rightBatch;
				
			}
			
		} catch (Exception e) {
			// TODO Auto-generated catch block
			
			//Roll back any outstanding batch updates
			try {
				this.connection.rollback();
			} catch (SQLException e1) {
				e1.printStackTrace();
			}
			
			//Print a stack trace
			e.printStackTrace();
			
		} finally {
			
			//Do auto commit
			try {
				this.connection.setAutoCommit(true);
			} catch (SQLException ex) {
				ex.printStackTrace();
			}

		}
		
		//Not doing any more work now
		this.isWorking = false;
		
	}
	
	/**
	 * Get the current action in human readable form
	 * 
	 * @return String
	 */
	public String getCurrentAction() {
		return this.currentAction;
	}
	
	/**
	 * Whether or not I am still doing some work
	 * 
	 * @return Boolean true if I am working
	 */
	public boolean isWorking() {
		return this.isWorking;
	}
	
	/**
	 * Loads a batch from the database and returns it
	 * 
	 * @return TellerBatch
	 */
	public TellerBatch loadBatchFromDatabase() throws IOException, SQLException, ClassNotFoundException {
		
		//Say what I am doing
		this.currentAction = "Loading batch from database...";
		
		//Create a statement
		Statement statement = connection.createStatement(ResultSet.TYPE_SCROLL_INSENSITIVE, ResultSet.CONCUR_READ_ONLY);
		
		//Select all ballotforms
		ResultSet rsBallotForms = statement.executeQuery("SELECT * FROM receipts WHERE election_id = " + this.race.election.electionID + " AND race_id = " + this.race.raceID + " AND teller_id = " + this.race.getLastBatchTellerID() + " AND teller_batch = 1");
		
		//Create a TellerBatch object
		TellerBatch resultBatch = new TellerBatch();
		
		//The number of ballot forms to add to batch
		rsBallotForms.last();
		this.totalBallotCount = rsBallotForms.getRow();
		this.ballotCount = 0;
		rsBallotForms.beforeFirst();
		System.out.println("Ballot forms to process: " + this.totalBallotCount);
		
		//Iterate through all ballotforms
		while(rsBallotForms.next()) {
			
			//Deserialise the partialform
			ObjectInputStream deserialisedPartialForm = new ObjectInputStream(new BufferedInputStream(rsBallotForms.getBinaryStream("receipt_partialform")));
			PartialForm currentPartialForm = (PartialForm)deserialisedPartialForm.readObject();
			
			//Add this PartialForm to the batch
			resultBatch.addBallotForm(currentPartialForm);
			
			//Increment counter
			this.ballotCount++;
			
		}
		
		System.out.println("Included " + ballotCount + " ballot forms in the batch loaded form the database.");
		
		//Finished, return
		return resultBatch;
		
	}
	
	
}

