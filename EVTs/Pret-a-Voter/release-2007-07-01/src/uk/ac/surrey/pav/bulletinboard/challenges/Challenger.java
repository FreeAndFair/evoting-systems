package uk.ac.surrey.pav.bulletinboard.challenges;

import java.math.BigInteger;
import java.sql.PreparedStatement;
import java.sql.SQLException;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.Random;

import javax.swing.JProgressBar;

import uk.ac.surrey.pav.bulletinboard.BulletinBoard;
import uk.ac.surrey.pav.bulletinboard.entities.Race;
import uk.ac.surrey.pav.bulletinboard.entities.Teller;
import uk.ac.surrey.pav.bulletinboard.exceptions.TellerDownException;

/**
 * Thread that challenges the tellers
 * 
 * @author David Lundin
 *
 */
public class Challenger implements Runnable {

	/**
	 * A bulletin board to use
	 */
	private BulletinBoard bulletinBoard;
	
	/**
	 * The race to challenge
	 */
	private Race race;
	
	/**
	 * A progress bar representing all th work done
	 */
	private JProgressBar progressBarTotal;
	
	/**
	 * A progress bar for the current action
	 */
	private JProgressBar progressBarCurrent;
	
	/**
	 * Constructor
	 * 
	 * @param bulletinBoard
	 * @param race
	 */
	public Challenger(BulletinBoard bulletinBoard, Race race, JProgressBar progressBarTotal, JProgressBar progressBarCurrent) {
		this.bulletinBoard = bulletinBoard;
		this.race = race;
		this.progressBarTotal = progressBarTotal;
		this.progressBarCurrent = progressBarCurrent;
		//System.out.println("Hi, I'm a challenger!");
	}

	/**
	 * What we do in this thread
	 */
	public void run() {

		try {

			//All the tellers
			Teller tellers[] = this.bulletinBoard.getTellerArray();

			/*
			 * For each teller, get commitment if they do not exist
			 */
			this.updateProgressBars("Getting commitments from tellers", 0, 0);
			for(int t = 0; t < tellers.length; t++) {
				
				//Update the progress bars
				int percentageDone = (int)(100*t/tellers.length);
				this.updateProgressBars("Getting commitment from " + tellers[t].name, percentageDone, 0);

				//If there is no challenge, get commitments
				if(this.race.getChallengeFromTellerID(tellers[t].tellerID) == null) {
					
					//Create a random 1000 byte array
					byte[] random = new byte[1000];
					Random randomiser = new Random();
					randomiser.nextBytes(random);
					
					//Get commitment from this teller
					byte[] currentCommitment = tellers[t].getCommitment(this.race.election.electionID, this.race.raceID, random);
					
					//Check that something was returned
					if(currentCommitment == null) {
						//Print out an error message
						System.out.println("Got no commitment from the teller.");
						
						//Return from the thread.run() method so as to stop
						return;
					}
					
					//Create a challenge object
					Challenge newChallenge = new Challenge(tellers[t].tellerID, currentCommitment, random);
					
					//Add the challenge to the list in this race
					this.race.addChallenge(newChallenge);
					
					//Save the challenge to the database
					this.saveChallenge(newChallenge);
					
				}

				//Update the progress bars
				percentageDone = (int)(100*(t+1)/tellers.length);
				this.updateProgressBars("Got commitment from " + tellers[t].name, percentageDone, 0);

			}
			
			/*
			 * Thus all challenges exist so we get values from tellers if they do not exist
			 */
			for(int t = 0; t < tellers.length; t++) {
				
				//Update the progress bars
				int percentageDone = (int)(100*t/tellers.length);
				this.updateProgressBars("Getting decommitted value from " + tellers[t].name, percentageDone, 1);

				//If there is no challenge, get commitments
				Challenge currentChallenge = this.race.getChallengeFromTellerID(tellers[t].tellerID);
				if(currentChallenge != null) {

					if(currentChallenge.bitmap == null) {

						//Collect value from teller
						NonceBitmapCouple newValue = tellers[t].getValue(this.race.election.electionID, this.race.raceID);
						
						if(newValue == null) {

							//Got nothing from the teller: print and exit
							System.out.println("Got no value from the teller");
							return;
							
						}
						
						//Set value to one collected from the teller
						this.race.updateChallenge(currentChallenge, newValue);
						
						//Update the challenge in the database
						this.updateChallenge(currentChallenge);

					}
					
				} else {
					
					//Error printout
					System.out.println("A commitment is missing!");
					
					//No challenge exists for this teller, major error: exit thread
					return;
					
				}
				
				//Update the progress bars
				percentageDone = (int)(100*(t+1)/tellers.length);
				this.updateProgressBars("Got decommitted value from " + tellers[t].name, percentageDone, 1);

			}
			
			/*
			 * XOR the committed values to create the mask
			 */

			//Update the progress bars
			this.updateProgressBars("Creating the mask", 0, 2);

			//The mask we are building
			BigInteger mask = new BigInteger("1");
			
			//Get an iterator of all the challenges
			Iterator challenges = this.race.challenges.iterator();
			if(challenges.hasNext()) {
				
				//Stick the first challenge into the mask
				Challenge currentChallenge = (Challenge)challenges.next(); 
				mask = new BigInteger(currentChallenge.bitmap);
				
				//Update the mask by XOR:ing all others into the mask
				while(challenges.hasNext()) {

					//Get the next challenge
					currentChallenge = (Challenge)challenges.next(); 

					//XOR this bitmap onto the mask
					mask.and(new BigInteger(currentChallenge.bitmap));
					
				}
				
				//The mask is now finished
				
			}

			/*
			 * Challenge each teller using this mask and store the result
			 */
			
			for(int t = 0; t < tellers.length; t++) {
				
				//Update the progress bars
				int percentageDone = (int)(100*t/tellers.length);
				this.updateProgressBars("Challenging " + tellers[t].name, percentageDone, 3);

				//Challenge the teller
				//TODO: The batchID in this call is always 0 because we do not use multiple batches per race
				ArrayList auditResult = tellers[t].audit(this.race.election.electionID, this.race.raceID, 0, mask);
				
				try {

					//Update the progress bars
					percentageDone = (int)(100*t/tellers.length);
					this.updateProgressBars("Storing audit info from " + tellers[t].name, percentageDone, 3);

					//Store the result to the database
					PreparedStatement insertAuditStatement = this.bulletinBoard.connection.prepareStatement("INSERT INTO receiptaudits (election_id, race_id, teller_id, left_receipt_position, right_receipt_position, audit_germ) VALUES (?, ?, ?, ?, ?, ?)");

					System.out.println("There are " + auditResult.size() + " auditResults.");
					
					//Insert each result into the database
					for(int c = 0; c < auditResult.size(); c++) {
						
						//Insert into db
						insertAuditStatement.setInt(1, this.race.election.electionID);
						insertAuditStatement.setInt(2, this.race.raceID);
						insertAuditStatement.setInt(3, tellers[t].tellerID);
						insertAuditStatement.setInt(4, ((LeftRightGerm)auditResult.get(c)).left);
						insertAuditStatement.setInt(5, ((LeftRightGerm)auditResult.get(c)).right);
						insertAuditStatement.setBytes(6, ((LeftRightGerm)auditResult.get(c)).germ);
						insertAuditStatement.execute();
						
					}
					
				} catch(SQLException e) {
					
					e.printStackTrace();
					
				}
				
				//Update the progress bars
				percentageDone = (int)(100*(t+1)/tellers.length);
				this.updateProgressBars("Challenged " + tellers[t].name, percentageDone, 3);

			}
			
		} catch (TellerDownException e) {
			
			//A teller is down: exit
			e.printStackTrace();
			
		}
		
	}
	
	/**
	 * Stores a challenge into the database
	 * 
	 * @param challenge
	 */
	private void saveChallenge(Challenge challenge) {

		try {
			
			//Store
			PreparedStatement insertCommitmentStatement = this.bulletinBoard.connection.prepareStatement("INSERT INTO commitments (election_id, race_id, teller_id, commitment_bulletinboard_nonce, commitment_commitment, commitment_received) VALUES (?, ?, ?, ?, ?, NOW())");
			insertCommitmentStatement.setInt(1, this.race.election.electionID);
			insertCommitmentStatement.setInt(2, this.race.raceID);
			insertCommitmentStatement.setInt(3, challenge.tellerID);
			insertCommitmentStatement.setBytes(4, challenge.bulletinBoardNonce);
			insertCommitmentStatement.setBytes(5, challenge.commitment);
			insertCommitmentStatement.execute();
			
		} catch (SQLException ex) {
			
			//Simply print a stack trace
			ex.printStackTrace();
			
		}

	}
	
	/**
	 * Update the stored challenge in the database
	 * 
	 * @param challenge
	 */
	private void updateChallenge(Challenge challenge) {
		
		try {
			
			PreparedStatement updateCommitmentStatement = this.bulletinBoard.connection.prepareStatement("UPDATE commitments SET commitment_teller_nonce = ?, commitment_bitmap = ? WHERE election_id = ? AND race_id = ? AND teller_id = ?");
			updateCommitmentStatement.setBytes(1, challenge.tellerNonce);
			updateCommitmentStatement.setBytes(2, challenge.bitmap);
			updateCommitmentStatement.setInt(3, this.race.election.electionID);
			updateCommitmentStatement.setInt(4, this.race.raceID);
			updateCommitmentStatement.setInt(5, challenge.tellerID);
			updateCommitmentStatement.execute();

		} catch (SQLException ex) {
			
			//Nothing to do except printing stack trace
			ex.printStackTrace();
			
		}
		
		
	}
	
	/**
	 * Updates the progress bars
	 * 
	 * @param currentAction
	 * @param percentage
	 * @param step
	 */
	private void updateProgressBars(String currentAction, int percentage, int step) {
		
		//Update the current progress bar
		this.progressBarCurrent.setValue(percentage);
		this.progressBarCurrent.setString(currentAction + " (" + percentage + "%)");
		
		//Update the total progress bar
		int numberOfSteps = 4;
		int totalPercentageDone = (100 * step / numberOfSteps) + (percentage / numberOfSteps);
		this.progressBarTotal.setValue(totalPercentageDone);
		this.progressBarTotal.setString(totalPercentageDone + "% of total process");

	}
	
}
