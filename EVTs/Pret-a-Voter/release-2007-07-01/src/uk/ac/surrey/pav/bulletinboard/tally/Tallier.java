package uk.ac.surrey.pav.bulletinboard.tally;

import java.io.BufferedInputStream;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;
import java.util.ArrayList;

import uk.ac.surrey.pav.ballotform.PartialForm;
import uk.ac.surrey.pav.ballotform.TellerBatch;
import uk.ac.surrey.pav.bulletinboard.entities.Candidate;
import uk.ac.surrey.pav.bulletinboard.entities.Race;

/**
 * The thread that tallies a race
 * 
 * @author David Lundin
 *
 */
public class Tallier implements Runnable {
	
	/**
	 * The race that is to be tallied
	 */
	private Race race;
	
	/**
	 * A database connection
	 */
	private Connection connection;
	
	/**
	 * The percentage of the votes needed to win
	 */
	private static int WINNING_PERCENTAGE = 50;

	/**
	 * Constructor
	 * 
	 * @param connection A database connection that the tallier will use
	 * @param race The race to tally
	 */
	public Tallier(Connection connection, Race race) {
		//Store references
		this.connection = connection;
		this.race = race;
	}
	
	/**
	 * All the ballot forms that have to be loaded from the database
	 */
	private int totalBallotCount = 0;
	
	/**
	 * The number of ballot forms loaded so far
	 */
	private int ballotCount = 0;
	
	/**
	 * Loads a batch from the database and then repeatedly tallies it until
	 * the required number of winners are found
	 */
	public void run() {

		try {
			
			/*
			 * LOAD THE FINAL BATCH FROM THE DATABASE
			 */
			
			//Create a statement
			Statement statement = this.connection.createStatement(ResultSet.TYPE_SCROLL_INSENSITIVE, ResultSet.CONCUR_READ_ONLY);
			
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
			
			/*
			 * Delete any previous tally from the database + set up statement to insert new tally
			 */
			
			//Delete any old tally
			Statement deleteStatement = this.connection.createStatement(ResultSet.TYPE_SCROLL_INSENSITIVE, ResultSet.CONCUR_READ_ONLY);
			deleteStatement.executeUpdate("DELETE FROM tallies WHERE election_id = " + this.race.election.electionID + " AND race_id = " + this.race.raceID + "");
			
			//An insert statement
			PreparedStatement tallyStatement = this.connection.prepareStatement("INSERT INTO tallies (election_id, race_id, tally_round, candidate_id, tally_votes) VALUES (?, ?, ?, ?, ?)");

			/*
			 * TALLY 
			 */
			
			//There is one ArrayList here for each candidate: one pile for each
			ArrayList[] ballots = new ArrayList[race.candidates.size()];
			for(int x=0; x<ballots.length; x++) {
				ballots[x] = new ArrayList();
			}
			
			//An arraylist for the pile of discarded receipts
			ArrayList discardedBallots = new ArrayList();
			
			//The total number of ballots
			int totalNumberOfBallots = resultBatch.ballotForms.size();
			
			//Sort the loaded ballotforms into the appropriate piles
			for(int x=0; x<resultBatch.ballotForms.size(); x++) {
				
				//Get the current form
				PartialForm currentForm = (PartialForm)resultBatch.ballotForms.get(x);
				
				//Check if the form does in fact not have any choices on it
				if(currentForm.isStillInCount()) {
					//It is still in play and may be sorted into a pile
					
					//Sort it
					ballots[currentForm.getCurrentTopChoice()].add(currentForm);
					
				} else {
					
					//It is in fact discarded and should be added to that pile
					discardedBallots.add(currentForm);
					
				}
				
			}
			
			//Create an integer array with the current score
			int[] currentScores = new int[ballots.length];
			for(int x=0; x<ballots.length; x++) {
				currentScores[x] = ballots[x].size();
			}

			//We are running as long as this is set to true
			boolean running = true;
			
			//A counter for the round
			int round = 0;
			
			//Delete the previous rounds
			this.race.tally.clear();

			//Keep repeating as long as necessary
			while(running) {
				
				//The text describing the round
				String description = "";
				
				//Increase round counter
				round++;
				
				//If this is not the first round and we are still running
				if(round > 1 && running) {
					
					//Someone should be eliminated. Find the lowest score over 0
					int currentLowest = 999999999;
					int currentLowestPosition = -1;
					for(int x=0; x<currentScores.length; x++) {
						//Go through all current scores
						
						//If this is lower than the current lowest but higher than 0
						if(currentScores[x] < currentLowest && currentScores[x] >= 0) {
							//Set as current lowest
							currentLowest = currentScores[x];
							currentLowestPosition = x;
						}
					}
					
					//Some debugging output
					System.out.println("Going on to eliminate " + currentLowestPosition);
					
					//Make sure a pile has been found (illogical not to find it)
					if(currentLowestPosition >= 0) {
					
						//EXTERMINATE!!

						//Description
						description = "Eliminated: " + ((Candidate)this.race.candidates.get(currentLowestPosition)).name;

						//Move all the ballotforms in the eliminated pile to the other piles
						//unless of course that pile is already eliminated
						System.out.println("There are " + ballots[currentLowestPosition].size() + " ballot forms in the pile that is to be eliminated.");

						for(int x=0; x<ballots[currentLowestPosition].size(); x++) {
							
							//Get the current form
							PartialForm currentForm = (PartialForm)ballots[currentLowestPosition].get(x);
							
							//Get the next non-eliminated pile
							while(currentForm.getNextTopChoice() && currentScores[currentForm.getCurrentTopChoice()] < 0) {
								//The secret is to do NOTHING!
							}
								
							if(currentForm.isStillInCount()) {

								//Add it to the pile
								//System.out.println("Next candidate: " + currentForm.getCurrentTopChoice());
								ballots[currentForm.getCurrentTopChoice()].add(currentForm);
									
								//Increase the number of votes in that pile
								currentScores[currentForm.getCurrentTopChoice()]++;

							} else {
								
								discardedBallots.add(currentForm);
								
							}
								
						}

						//Mark the pile as eliminated
						currentScores[currentLowestPosition] = -1;
						ballots[currentLowestPosition] = null;

					} else {
						
						//We didn't find one, so quit
						running = false;
						
					}
					
				}
				
				//Has anyone won? Check if anyone has the required percentage
				for(int x=0; x<currentScores.length; x++) {
					
					//Check if the required proportion of the votes has been reached
					if((float)currentScores[x] >= (float)totalNumberOfBallots * ((float)WINNING_PERCENTAGE / 100.00)) {
						
						//Someone has won so stop running
						running = false;
						
						//Description
						//description = ((Candidate)this.race.candidates.get(x)).name + " is a winner.";
						
					}
					
				}

				//Create round record in memory
				this.race.tally.addRound("Round " + round, currentScores, discardedBallots.size(), description);
				
				//Store round in database
				for(int x=0; x < currentScores.length; x++) {
					
					System.out.println("Storing tally score " + x + ": " + currentScores[x]);
					
					tallyStatement.setInt(1, this.race.election.electionID);
					tallyStatement.setInt(2, this.race.raceID);
					tallyStatement.setInt(3, round);
					tallyStatement.setInt(4, x);
					tallyStatement.setInt(5, currentScores[x]);
					tallyStatement.execute();
					
				}

			}
			

		} catch (SQLException ex) {
			ex.printStackTrace();
		} catch (IOException ex) {
			ex.printStackTrace();
		} catch (ClassNotFoundException ex) {
			ex.printStackTrace();
		}

	}

}
