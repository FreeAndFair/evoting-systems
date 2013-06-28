package uk.ac.surrey.pav.bulletinboard;

import java.io.BufferedInputStream;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.UnsupportedEncodingException;
import java.rmi.RemoteException;
import java.rmi.server.UnicastRemoteObject;
import java.security.InvalidKeyException;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.security.Signature;
import java.security.SignatureException;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.Random;

import uk.ac.surrey.pav.administrator.registry.Voter;
import uk.ac.surrey.pav.administrator.registry.VoterBallotFormPaper;
import uk.ac.surrey.pav.ballotform.BallotForm;
import uk.ac.surrey.pav.ballotform.BallotFormPaper;
import uk.ac.surrey.pav.ballotform.CharacterPermutation;
import uk.ac.surrey.pav.ballotform.Onion;
import uk.ac.surrey.pav.ballotform.Permutation;
import uk.ac.surrey.pav.ballotform.Receipt;
import uk.ac.surrey.pav.ballotform.Vote;
import uk.ac.surrey.pav.bulletinboard.entities.AuditMachine;
import uk.ac.surrey.pav.bulletinboard.entities.Booth;
import uk.ac.surrey.pav.bulletinboard.entities.Election;
import uk.ac.surrey.pav.bulletinboard.entities.Race;
import uk.ac.surrey.pav.bulletinboard.entities.Teller;
import uk.ac.surrey.pav.bulletinboard.exceptions.TellerDownException;
import uk.ac.surrey.pav.bulletinboard.exceptions.TellerMalfunctionException;
import uk.ac.surrey.pav.common.HexConstructor;

/**
 * Acts as a web bulletin board server over RMI
 * 
 * @author David Lundin
 *
 */
public class BulletinBoardServer extends UnicastRemoteObject implements BulletinBoardInterface  {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	
	/**
	 * The bulletin board class holding all information
	 * about the election currently being run
	 */
	private BulletinBoard bulletinBoard;

	/**
	 * Default constructor
	 * 
	 * @param bulletinBoard		The bulletin board with info about election
	 * @throws RemoteException
	 */
	public BulletinBoardServer(BulletinBoard bulletinBoard) throws RemoteException {
		//Store reference to the bulletin board
		this.bulletinBoard = bulletinBoard;
	}

	/**
	 * Posts a vote
	 * 
	 * @param vote
	 * @return Receipt
	 */
	public Receipt postBallot(Vote vote) {

		try {
			
			/*
			 * CHECK THE SIGNATURE OF THE VOTING BOOTH 
			 */
			
			//Get the booth public key
			Booth currentBooth = this.bulletinBoard.getBoothFromID(vote.boothID);
			if(currentBooth == null) {
				return new Receipt(Receipt.ERROR_NOT_A_BOOTH, vote.id, vote.signedHash, vote.signedHash, vote.permutations, "No booth with this ID is loaded", this.bulletinBoard.privateKey);
			}
	
	        //Test the signature
	        if(!vote.checkSignature(currentBooth.publicKey)) {
	        	return new Receipt(Receipt.ERROR_NOT_A_BOOTH, vote.id, vote.signedHash, vote.signedHash, vote.permutations, "Signature check failed.", this.bulletinBoard.privateKey);
	        }
		        
	        /*
	         * Get the ballot form paper and the associated ballot forms
	         */

	        //Create a statement
			Statement statement = this.bulletinBoard.connection.createStatement(ResultSet.TYPE_SCROLL_INSENSITIVE, ResultSet.CONCUR_READ_ONLY);
	
			//Query database
			ResultSet rsBallotFormPaper = statement.executeQuery("SELECT * FROM ballotformpapers WHERE ballotformpaper_id = " + vote.id);
			
			//Check if there is a ballot form with this ID in the database - if not, throw InvalidBallotFormException
			if(!rsBallotFormPaper.next()) {
				System.out.println("Could not find any ballot forms for this ballot form paper.");
				return new Receipt(Receipt.ERROR_INVALID_BALLOT_FORM, vote.id, vote.signedHash, vote.signedHash, vote.permutations, "No ballot form paper with this ID in the database.", this.bulletinBoard.privateKey);
			}
			
			//Check the status of the ballot form
			String ballotFormPaperStatus = rsBallotFormPaper.getString("ballotformpaper_status");
			if(!ballotFormPaperStatus.equals(BallotForm.STATUS_AVAILABLE)) {
				System.out.println("This ballot form has been used.");
				return new Receipt(Receipt.ERROR_BALLOT_FORM_USED, vote.id, vote.signedHash, vote.signedHash, vote.permutations, "This ballot form is not available for submission. Its status is: " + ballotFormPaperStatus, this.bulletinBoard.privateKey);
			}
			
			/*
			 * Store vars
			 */
			
			//The ballot form paper id
			int ballotFormPaperID = rsBallotFormPaper.getInt("ballotformpaper_id");

			//Deserialise the hash
			ObjectInputStream ois = new ObjectInputStream(new BufferedInputStream(rsBallotFormPaper.getBinaryStream("ballotformpaper_hash")));
			byte[] ballotFormHash = (byte[])ois.readObject();
			//System.out.println("Hash on the ballot form: " + HexConstructor.byteArrayToHexString(ballotFormHash));

			/*
			 * CHECK THAT THE HASH AND SIGNATURE CORRESPONDS WITH THE POSTED VALUES
			 */
			
			//Unsign the signed hash from the ballot form 
			byte[] unsignedHash = BallotFormPaper.removeHashSignature(vote.signedHash, this.bulletinBoard.administratorPublicKey);
			//System.out.println("        The signed hash: " + HexConstructor.byteArrayToHexString(vote.signedHash));
			//System.out.println("      The unsigned hash: " + HexConstructor.byteArrayToHexString(unsignedHash));
			//System.out.println("             comparison: " + HexConstructor.byteArrayToHexString(unsignedHash).compareTo(HexConstructor.byteArrayToHexString(ballotFormHash)));

			//Check that the hash where the signature has been removed is the same as the hash in the form
			if(HexConstructor.byteArrayToHexString(unsignedHash).compareTo(HexConstructor.byteArrayToHexString(ballotFormHash)) != 0) {
				return new Receipt(Receipt.ERROR_INVALID_HASH, vote.id, unsignedHash, vote.signedHash, vote.permutations, "Hash check failed.", this.bulletinBoard.privateKey);
			}
			
			//Serialize the vote object to store in the database
			ByteArrayOutputStream baos = new ByteArrayOutputStream();
		    ObjectOutputStream oout = new ObjectOutputStream(baos);
		    oout.writeObject(vote);
		    oout.close();

			//Mark the ballot form paper as VOTE_IN_PROGRESS in the database
			PreparedStatement updateBallotFormPaperStatusStatement = this.bulletinBoard.connection.prepareStatement("UPDATE ballotformpapers SET ballotformpaper_status = ?, ballotformpaper_statuschangedate = NOW(), vote_object = ? WHERE ballotformpaper_id = ?");
			updateBallotFormPaperStatusStatement.setString(1, "VOTE_IN_PROGRESS");
			updateBallotFormPaperStatusStatement.setBytes(2, baos.toByteArray());
			updateBallotFormPaperStatusStatement.setInt(3, ballotFormPaperID);
			updateBallotFormPaperStatusStatement.execute();

	        /*
	         * All is good now, proceed to posting the supplied ballot forms
	         */

			//Query database for the associated ballot forms
			ResultSet rsBallotForms = statement.executeQuery("SELECT f.* FROM ballotforms f, ballotformsinpapers i WHERE f.ballotform_serialno = i.ballotform_id AND i.ballotformpaper_id = " + ballotFormPaperID + " AND ballotform_status = 'AVAILABLE' ORDER BY i.position ASC");

			//Check the number of ballot forms
			rsBallotForms.last();
			int numberOfBallotForms = rsBallotForms.getRow();
			rsBallotForms.beforeFirst();

			//Check that there ARE ballot forms
			if(numberOfBallotForms == 0) {
				System.out.println("Could not find any ballot forms for this ballotformpaper when trying to post the votes.");
				return new Receipt(Receipt.ERROR_INVALID_BALLOT_FORM, vote.id, unsignedHash, vote.signedHash, vote.permutations, "There were no ballot forms for this ballotformpaper.", this.bulletinBoard.privateKey);
			}

	        //Check that there are exactly the right number of votes
	        if(vote.permutations.size() != numberOfBallotForms) {
				System.out.println("The number of votes coming in (" + vote.permutations.size() + ") did not match the number of races on the form (" + numberOfBallotForms + ".");
	        	return new Receipt(Receipt.ERROR_INVALID_BALLOT_FORM, vote.id, unsignedHash, vote.signedHash, vote.permutations, "The vote had " + vote.permutations.size() + " permutations but there are " + numberOfBallotForms + " ballot forms.", this.bulletinBoard.privateKey);
	        }

	        //Get an iterator for the permutations
	        Iterator permutationIterator = vote.permutations.iterator();
	        
	        //Go through all the forms and update them
	        while(rsBallotForms.next()) {
	        	
	        	//The permutation for this ballot form
	        	CharacterPermutation currentPermutation = (CharacterPermutation)permutationIterator.next();
	        	
				//De-serialise the BallotForm object from the database
				ObjectInputStream deserialisedBallotForm = new ObjectInputStream(new BufferedInputStream(rsBallotForms.getBinaryStream("ballotform_object")));
				BallotForm currentBallotForm = (BallotForm)deserialisedBallotForm.readObject();

				//Get the current election
				Election currentElection = this.bulletinBoard.getElectionFromID(currentBallotForm.votingForm.signedOnion.raceInfo.election);
				if(currentElection == null) {
					System.out.println("The election in the ballot form does not exist.");
					return new Receipt(Receipt.ERROR_INVALID_BALLOT_FORM, vote.id, unsignedHash, vote.signedHash, vote.permutations, "The election in the ballot form does not exist.", this.bulletinBoard.privateKey);
				}
				
				//Check if this election is currently accepting ballots
				if(!currentElection.isAcceptingVotes()) {
					System.out.println("This election is not accepting any votes.");
					return new Receipt(Receipt.ERROR_INVALID_BALLOT_FORM, vote.id, unsignedHash, vote.signedHash, vote.permutations, "This election is currently not accepting ballots.", this.bulletinBoard.privateKey);
				}
				
				//Get the current race
				Race currentRace = currentElection.getRaceFromID(currentBallotForm.votingForm.signedOnion.raceInfo.race);
				if(currentRace == null) {
					System.out.println("The race in the ballot form does not exist.");
					return new Receipt(Receipt.ERROR_INVALID_BALLOT_FORM, vote.id, unsignedHash, vote.signedHash, vote.permutations, "The race in the ballot form does not exist.", this.bulletinBoard.privateKey);
				}
				
				//Check if the permutations are of similar length
				if(!currentPermutation.testEqualNumberOfCandidates(currentRace.getBaseOrderPermutation())) {
					System.out.println("The voter's choice (" + currentPermutation.permutation.length + ") does not correspond to the number of candidates in this race (" + currentRace.getBaseOrderPermutation().permutation.length + "," + currentRace.candidates.size() + "). Election " + currentElection.electionID + " race " + currentRace.raceID + "(" + currentBallotForm.votingForm.signedOnion.raceInfo.race + ")");;
					return new Receipt(Receipt.ERROR_INVALID_BALLOT_FORM, vote.id, unsignedHash, vote.signedHash, vote.permutations, "The voter's choice (" + currentPermutation.permutation.length + ") does not correspond to the number of candidates in this race (" + currentRace.getBaseOrderPermutation().permutation.length + "," + currentRace.candidates.size() + "). Election " + currentElection.electionID + " race " + currentRace.raceID + "(" + currentBallotForm.votingForm.signedOnion.raceInfo.race + ")" , this.bulletinBoard.privateKey);
				}
				
				//Set the Permutation on the VotingForm to the one received
				currentBallotForm.setVote(currentPermutation);
				
				//Set the status in the VotingForm to VOTED
				currentBallotForm.votingForm.status = "VOTED";
				
				//Re-serialise the BallotForm object
				baos = new ByteArrayOutputStream();
			    oout = new ObjectOutputStream(baos);
			    oout.writeObject(currentBallotForm);
			    oout.close();
				
				//Store the BallotForm in the database and change the status in the database to VOTED
				//and store the boothID against the form as well as the status change date
			    //TODO: This should update in a batch that may be rolled back!!
				PreparedStatement updateStatement = this.bulletinBoard.connection.prepareStatement("UPDATE ballotforms SET ballotform_status = ?, booth_id = ?, ballotform_object = ?, ballotform_plaintext_vote = ?, ballotform_statuschangedate = NOW() WHERE ballotform_serialno = ?");
				updateStatement.setString(1, "VOTED");
				updateStatement.setInt(2, vote.boothID);
				updateStatement.setBytes(3, baos.toByteArray());
				updateStatement.setString(4, currentBallotForm.votingForm.vote.toString());
				updateStatement.setInt(5, currentBallotForm.serialNo);
				updateStatement.execute();
				System.out.println("Vote to store to db: " + currentBallotForm.votingForm.vote.toString());
				
				//Increment the number of votes cast
				currentBooth.incrementBallotCount();
				currentRace.incrementBallotCount();
	        	
	        }
			
			/*
			 * The vote was successfully posted!!
			 */
	        
			//Mark the ballot form paper as voted in the database
			updateBallotFormPaperStatusStatement = this.bulletinBoard.connection.prepareStatement("UPDATE ballotformpapers SET ballotformpaper_status = ?, ballotformpaper_statuschangedate = NOW() WHERE ballotformpaper_id = ?");
			updateBallotFormPaperStatusStatement.setString(1, "VOTED");
			updateBallotFormPaperStatusStatement.setInt(2, ballotFormPaperID);
			updateBallotFormPaperStatusStatement.execute();

	        //Return a receipt
			return new Receipt(Receipt.CORRECTLY_POSTED_RECEIPT, vote.id, unsignedHash, vote.signedHash, vote.permutations, this.bulletinBoard.privateKey);
			
			
		} catch (InvalidKeyException e) {
			return new Receipt(Receipt.ERROR_NOT_A_BOOTH, vote.id, vote.signedHash, vote.signedHash, vote.permutations, "InvalidKeyException: " + e.getMessage(), this.bulletinBoard.privateKey);
		} catch (SQLException e) {
			return new Receipt(Receipt.ERROR_DATABASE_PROBLEM, vote.id, vote.signedHash, vote.signedHash, vote.permutations, "SQLException: " + e.getMessage(), this.bulletinBoard.privateKey);
		} catch (IOException e) {
			return new Receipt(Receipt.ERROR_INTERNAL_BULLETIN_BOARD_PROBLEM, vote.id, vote.signedHash, vote.signedHash, vote.permutations, "IOException: " + e.getMessage(), this.bulletinBoard.privateKey);
		} catch (ClassNotFoundException e) {
			return new Receipt(Receipt.ERROR_INTERNAL_BULLETIN_BOARD_PROBLEM, vote.id, vote.signedHash, vote.signedHash, vote.permutations, "ClassNotFoundException: " + e.getMessage(), this.bulletinBoard.privateKey);
		}
		
	}
	
	public Receipt auditForm(Vote vote) throws RemoteException {
		
		try {
			
			/*
			 * CHECK THE SIGNATURE OF THE VOTING BOOTH 
			 */
			
			//Get the booth public key
			AuditMachine currentAuditMachine = this.bulletinBoard.getAuditMachineFromID(vote.boothID);
			if(currentAuditMachine == null) {
				System.out.println("No booth with this ID is loaded");
				return new Receipt(Receipt.ERROR_NOT_A_BOOTH, vote.id, vote.signedHash, vote.signedHash, "No booth with this ID is loaded", this.bulletinBoard.privateKey);
			}
	
	        //Test the signature
	        if(!vote.checkSignature(currentAuditMachine.publicKey)) {
				System.out.println();
	        	return new Receipt(Receipt.ERROR_NOT_A_BOOTH, vote.id, vote.signedHash, vote.signedHash, "Signature check failed: you are not an audit machine", this.bulletinBoard.privateKey);
	        }
		        
	        /*
	         * Get the ballot form paper and the associated ballot forms
	         */

	        //Create a statement
			Statement statement = this.bulletinBoard.connection.createStatement(ResultSet.TYPE_SCROLL_INSENSITIVE, ResultSet.CONCUR_READ_ONLY);
	
			//Query database
			ResultSet rsBallotFormPaper = statement.executeQuery("SELECT * FROM ballotformpapers WHERE ballotformpaper_id = " + vote.id);
			
			//Check if there is a ballot form with this ID in the database - if not, throw InvalidBallotFormException
			if(!rsBallotFormPaper.next()) {
				System.out.println();
				return new Receipt(Receipt.ERROR_INVALID_BALLOT_FORM, vote.id, vote.signedHash, vote.signedHash, "No ballot form paper with this ID in the database.", this.bulletinBoard.privateKey);
			}
			
			//Check the status of the ballot form
			String ballotFormPaperStatus = rsBallotFormPaper.getString("ballotformpaper_status");
			if(!ballotFormPaperStatus.equals(BallotForm.STATUS_AVAILABLE)) {
				System.out.println();
				return new Receipt(Receipt.ERROR_BALLOT_FORM_USED, vote.id, vote.signedHash, vote.signedHash, "This ballot form is not available for submission. Its status is: " + ballotFormPaperStatus, this.bulletinBoard.privateKey);
			}

			/*
			 * Store vars
			 */
			
			//The ballot form paper id
			int ballotFormPaperID = rsBallotFormPaper.getInt("ballotformpaper_id");

			//Deserialise the hash
			ObjectInputStream ois = new ObjectInputStream(new BufferedInputStream(rsBallotFormPaper.getBinaryStream("ballotformpaper_hash")));
			byte[] ballotFormHash = (byte[])ois.readObject();
			//System.out.println("Hash on the ballot form: " + HexConstructor.byteArrayToHexString(ballotFormHash));

			/*
			 * CHECK THAT THE HASH AND SIGNATURE CORRESPONDS WITH THE POSTED VALUES
			 */
			
			//Unsign the signed hash from the ballot form 
			byte[] unsignedHash = BallotFormPaper.removeHashSignature(vote.signedHash, this.bulletinBoard.administratorPublicKey);
			//System.out.println("        The signed hash: " + HexConstructor.byteArrayToHexString(vote.signedHash));
			//System.out.println("      The unsigned hash: " + HexConstructor.byteArrayToHexString(unsignedHash));
			//System.out.println("             comparison: " + HexConstructor.byteArrayToHexString(unsignedHash).compareTo(HexConstructor.byteArrayToHexString(ballotFormHash)));

			//Check that the hash where the signature has been removed is the same as the hash in the form
			if(HexConstructor.byteArrayToHexString(unsignedHash).compareTo(HexConstructor.byteArrayToHexString(ballotFormHash)) != 0) {
				System.out.println("Hash check failed.");
				return new Receipt(Receipt.ERROR_INVALID_HASH, vote.id, unsignedHash, vote.signedHash, "Hash check failed.", this.bulletinBoard.privateKey);
			}
			
			//Serialize the vote object to store in the database
			ByteArrayOutputStream baos = new ByteArrayOutputStream();
		    ObjectOutputStream oout = new ObjectOutputStream(baos);
		    oout.writeObject(vote);
		    oout.close();

			//Mark the ballot form paper as audit in progress
			PreparedStatement updateBallotFormPaperStatusStatement = this.bulletinBoard.connection.prepareStatement("UPDATE ballotformpapers SET ballotformpaper_status = ?, ballotformpaper_statuschangedate = NOW(), vote_object = ? WHERE ballotformpaper_id = ?");
			updateBallotFormPaperStatusStatement.setString(1, "AUDIT_IN_PROGRESS");
			updateBallotFormPaperStatusStatement.setBytes(2, baos.toByteArray());
			updateBallotFormPaperStatusStatement.setInt(3, ballotFormPaperID);
			updateBallotFormPaperStatusStatement.execute();

	        /*
	         * All is good now, proceed to auditing the forms
	         */

			//Query database for the associated ballot forms
			ResultSet rsBallotForms = statement.executeQuery("SELECT f.* FROM ballotforms f, ballotformsinpapers i WHERE f.ballotform_serialno = i.ballotform_id AND i.ballotformpaper_id = " + ballotFormPaperID + " AND ballotform_status = 'AVAILABLE' ORDER BY i.position ASC");

			//Check the number of ballot forms
			rsBallotForms.last();
			int numberOfBallotForms = rsBallotForms.getRow();
			rsBallotForms.beforeFirst();

			//Check that there ARE ballot forms
			if(numberOfBallotForms == 0) {
				System.out.println("There were no ballot forms for this ballotformpaper.");
				return new Receipt(Receipt.ERROR_INVALID_BALLOT_FORM, vote.id, unsignedHash, vote.signedHash, "There were no ballot forms for this ballotformpaper.", this.bulletinBoard.privateKey);
			}
			
			//A list of all the ballot forms that are audited later
			ArrayList ballotForms = new ArrayList();

	        //Go through all the forms and audit them
	        while(rsBallotForms.next()) {
	        	
				//De-serialise the BallotForm object from the database
				ObjectInputStream deserialisedBallotForm = new ObjectInputStream(new BufferedInputStream(rsBallotForms.getBinaryStream("ballotform_object")));
				BallotForm currentBallotForm = (BallotForm)deserialisedBallotForm.readObject();

				//Get the current election
				Election currentElection = this.bulletinBoard.getElectionFromID(currentBallotForm.votingForm.signedOnion.raceInfo.election);
				if(currentElection == null) {
					System.out.println("The election in the ballot form does not exist.");
					return new Receipt(Receipt.ERROR_INVALID_BALLOT_FORM, vote.id, unsignedHash, vote.signedHash, "The election in the ballot form does not exist.", this.bulletinBoard.privateKey);
				}
				
				//Get the current race
				Race currentRace = currentElection.getRaceFromID(currentBallotForm.votingForm.signedOnion.raceInfo.race);
				if(currentRace == null) {
					System.out.println("The race in the ballot form does not exist.");
					return new Receipt(Receipt.ERROR_INVALID_BALLOT_FORM, vote.id, unsignedHash, vote.signedHash, "The race in the ballot form does not exist.", this.bulletinBoard.privateKey);
				}
				
				//Set the status in the VotingForm to AUDITED
				currentBallotForm.votingForm.status = "AUDITED";
				
				//Re-serialise the BallotForm object
				baos = new ByteArrayOutputStream();
			    oout = new ObjectOutputStream(baos);
			    oout.writeObject(currentBallotForm);
			    oout.close();
				
				//Store the BallotForm in the database and change the status in the database to AUDITED
				//and store the boothID against the form as well as the status change date
				PreparedStatement updateStatement = this.bulletinBoard.connection.prepareStatement("UPDATE ballotforms SET ballotform_status = ?, booth_id = ?, ballotform_object = ?, ballotform_statuschangedate = NOW() WHERE ballotform_serialno = ?");
				updateStatement.setString(1, "AUDIT_IN_PROGRESS");
				updateStatement.setInt(2, vote.boothID);
				updateStatement.setBytes(3, baos.toByteArray());
				updateStatement.setInt(4, currentBallotForm.serialNo);
				updateStatement.execute();
				
				//Store reference
				ballotForms.add(currentBallotForm);
				
				//Increment the number of votes cast
				currentAuditMachine.incrementBallotCount();
				currentElection.incrementBallotAuditCount();
	        	
	        }
	        
	        /*
	         * GO AHEAD TO SENDING THE AUDITS TO THE TELLERS
	         */
	        
	        //The permutations to return
	        ArrayList permutationsForReceipt = new ArrayList();
	        
	        //Go through the ballot forms
	        for(int b = 0; b < ballotForms.size(); b++) {
	        	
	        	//The ballot form
	        	BallotForm currentBallotForm = (BallotForm)ballotForms.get(b);
	        	
				//Statement for inserting audit info into database
				PreparedStatement insertAuditStatement = this.bulletinBoard.connection.prepareStatement("INSERT INTO ballotformaudits (ballotform_serialno, teller_id, teller_batch, audit_germ, audit_onion, audit_permutation, audit_plaintext_permutation) VALUES (?, ?, ?, ?, ?, ?, ?)");
		
				//Store a list of all the permutations
				ArrayList permutationList = new ArrayList();
				
				//Get the full onion
				Onion currentOnion = currentBallotForm.votingForm.signedOnion.onion;

				//Get the current election
				Election currentElection = this.bulletinBoard.getElectionFromID(currentBallotForm.votingForm.signedOnion.raceInfo.election);
				if(currentElection == null) {
					System.out.println("The election in the ballot form does not exist.");
					return new Receipt(Receipt.ERROR_INVALID_BALLOT_FORM, vote.id, unsignedHash, vote.signedHash, vote.permutations, "The election in the ballot form does not exist.", this.bulletinBoard.privateKey);
				}

				//Get the current race
				Race currentRace = currentElection.getRaceFromID(currentBallotForm.votingForm.signedOnion.raceInfo.race);
				if(currentRace == null) {
					System.out.println("The race in the ballot form does not exist.");
					return new Receipt(Receipt.ERROR_INVALID_BALLOT_FORM, vote.id, unsignedHash, vote.signedHash, vote.permutations, "The race in the ballot form does not exist.", this.bulletinBoard.privateKey);
				}

				//Go through all tellers IN THE REVERSE ORDER
				for(int x=this.bulletinBoard.getTellerCount()-1; x>=0; x--) {
					
					//Get reference to teller
					Teller currentTeller = this.bulletinBoard.getTeller(x);
					
					//Get something from the teller
					ArrayList result = currentTeller.reveal(currentOnion);
					
					//Check if we have a result
					if(result == null) {
						System.out.println("Teller " + currentTeller.tellerID + " did not return anything when queried.");
						throw new TellerDownException("Teller " + currentTeller.tellerID + " did not return anything when queried.", currentTeller.tellerID);
					}
					if(result.size() != 6) {
						System.out.println("Teller " + currentTeller.tellerID + " returned the wrong number of items.");
						throw new TellerDownException("Teller " + currentTeller.tellerID + " returned the wrong number of items.", currentTeller.tellerID);
					}
		
					//Check that the result is what we expect
					if(!(	result.get(0) instanceof Permutation
							&& result.get(1) instanceof byte[]
							&& result.get(2) instanceof Onion
							&& result.get(3) instanceof Permutation
							&& result.get(4) instanceof byte[]
							&& result.get(5) instanceof Onion)) {
						System.out.println("The teller returned unknown data.");
						throw new TellerMalfunctionException("The teller returned unknown data.");
					}
					
					//References to data
					Permutation firstPermutation = (Permutation)result.get(0);
					byte[] firstGerm = (byte[])result.get(1);
					Onion firstOnion = (Onion)result.get(2);
					Permutation secondPermutation = (Permutation)result.get(3);
					byte[] secondGerm = (byte[])result.get(4);
					Onion secondOnion = (Onion)result.get(5);
					
					//Store new onion
					currentOnion = secondOnion;
					
					/*
					 * POST THE AUDIT INFORMATION TO THE DATABASE
					 */
					
				    //THE FIRST LAYER
					insertAuditStatement.setInt(1, currentBallotForm.serialNo);
					insertAuditStatement.setInt(2, currentTeller.tellerID);
					insertAuditStatement.setInt(3, 0);
					insertAuditStatement.setBytes(4, firstGerm);
					
					//The onion
					baos = new ByteArrayOutputStream();
				    oout = new ObjectOutputStream(baos);
				    oout.writeObject(firstOnion);
					insertAuditStatement.setBytes(5, baos.toByteArray());
					
					//The permutation
					baos = new ByteArrayOutputStream();
				    oout = new ObjectOutputStream(baos);
				    oout.writeObject(firstPermutation);
					insertAuditStatement.setBytes(6, baos.toByteArray());
					insertAuditStatement.setString(7, firstPermutation.toString());
					
					//Post to database
					insertAuditStatement.execute();

				    //THE SECOND LAYER
					insertAuditStatement.setInt(1, currentBallotForm.serialNo);
					insertAuditStatement.setInt(2, currentTeller.tellerID);
					insertAuditStatement.setInt(3, 1);
					insertAuditStatement.setBytes(4, secondGerm);
					
					//The onion
					baos = new ByteArrayOutputStream();
				    oout = new ObjectOutputStream(baos);
				    oout.writeObject(secondOnion);
					insertAuditStatement.setBytes(5, baos.toByteArray());
					
					//The permutation
					baos = new ByteArrayOutputStream();
				    oout = new ObjectOutputStream(baos);
				    oout.writeObject(secondPermutation);
					insertAuditStatement.setBytes(6, baos.toByteArray());
					insertAuditStatement.setString(7, secondPermutation.toString());
					
					//Post to database
					insertAuditStatement.execute();

					//Close the output stream
				    oout.close();
				    baos.close();

					//Store this permutation for the recreation of the candidate list 
					permutationList.add(firstPermutation);
					permutationList.add(secondPermutation);
					
					//Mark ballot form as audited in the database
					PreparedStatement updateStatement = this.bulletinBoard.connection.prepareStatement("UPDATE ballotforms SET ballotform_status = ?, ballotform_statuschangedate = NOW() WHERE ballotform_serialno = ?");
					updateStatement.setString(1, "AUDITED");
					updateStatement.setInt(2, currentBallotForm.serialNo);
					updateStatement.execute();

					
				}

				//Get base order permutation as the initial permutation
				Permutation resultPermutation = currentRace.getBaseOrderPermutation();

				//Apply all the permutations in reverse order
				System.out.println("Going to apply " + permutationList.size() + " permutations now.");
				for(int x = permutationList.size() - 1; x >= 0; x--) {
					Permutation currentPermutation = (Permutation)permutationList.get(x);
					System.out.println("Current order:" + resultPermutation.toString() + ", applying: " + currentPermutation.toString());
					resultPermutation.permute(currentPermutation);
				}
				
				//Add the permutation to the list of permutations
				permutationsForReceipt.add(resultPermutation);

	        }
			
			/*
			 * The vote was successfully audited!!
			 */
	        
			//Mark the ballot form paper as audited
			updateBallotFormPaperStatusStatement.setString(1, "AUDITED");
			updateBallotFormPaperStatusStatement.setInt(2, ballotFormPaperID);
			updateBallotFormPaperStatusStatement.execute();
			
	        //Return a receipt
			return new Receipt(Receipt.AUDIT_RECEIPT, vote.id, unsignedHash, vote.signedHash, permutationsForReceipt, this.bulletinBoard.privateKey);
			
			
		} catch (InvalidKeyException e) {
			return new Receipt(Receipt.ERROR_NOT_A_BOOTH, vote.id, vote.signedHash, vote.signedHash, vote.permutations, "InvalidKeyException: " + e.getMessage(), this.bulletinBoard.privateKey);
		} catch (SQLException e) {
			return new Receipt(Receipt.ERROR_DATABASE_PROBLEM, vote.id, vote.signedHash, vote.signedHash, vote.permutations, "SQLException: " + e.getMessage(), this.bulletinBoard.privateKey);
		} catch (IOException e) {
			return new Receipt(Receipt.ERROR_INTERNAL_BULLETIN_BOARD_PROBLEM, vote.id, vote.signedHash, vote.signedHash, vote.permutations, "IOException: " + e.getMessage(), this.bulletinBoard.privateKey);
		} catch (ClassNotFoundException e) {
			return new Receipt(Receipt.ERROR_INTERNAL_BULLETIN_BOARD_PROBLEM, vote.id, vote.signedHash, vote.signedHash, vote.permutations, "ClassNotFoundException: " + e.getMessage(), this.bulletinBoard.privateKey);
		} catch (TellerDownException e) {
			return new Receipt(Receipt.ERROR_TELLER_DOWN, vote.id, vote.signedHash, vote.signedHash, vote.permutations, e.getMessage(), this.bulletinBoard.privateKey);
		} catch (TellerMalfunctionException e) {
			return new Receipt(Receipt.ERROR_TELLER_DOWN, vote.id, vote.signedHash, vote.signedHash, vote.permutations, e.getMessage(), this.bulletinBoard.privateKey);
		}
		
	}

	/**
	 * Assigns a form to a voter in the database
	 */
	public Voter assignFormToVoter(Voter voter, int serialNumber) throws RemoteException {

		try {

	        //Check if voter is assigned another form
			Statement statement = this.bulletinBoard.connection.createStatement(ResultSet.TYPE_SCROLL_INSENSITIVE, ResultSet.CONCUR_READ_ONLY);
			ResultSet rsVoterBallotForms = statement.executeQuery("SELECT COUNT(*) AS currentforms FROM voterballotformpapers v WHERE v.voter_id = " + voter.databaseID + " AND vbfp_current = 1");
			
			if(rsVoterBallotForms.next()) {

				if(rsVoterBallotForms.getInt("currentforms") == 0) {

			        //Check that this form is AVAILABLE and that it is not assigned to another voter
					Statement ballotFormStatement = this.bulletinBoard.connection.createStatement(ResultSet.TYPE_SCROLL_INSENSITIVE, ResultSet.CONCUR_READ_ONLY);
					ResultSet rsBallotForm = ballotFormStatement.executeQuery("SELECT COUNT(*) AS numberofforms FROM ballotformpapers WHERE ballotformpaper_id = " + serialNumber + " AND ballotformpaper_id NOT IN (SELECT ballotformpaper_id FROM voterballotformpapers) AND ballotformpaper_status = 'AVAILABLE'");

					if(rsBallotForm.next() && rsBallotForm.getInt("numberofforms") == 1) {
						
						//Store this as the current form
						PreparedStatement insertStatement = this.bulletinBoard.connection.prepareStatement("INSERT INTO voterballotformpapers (voter_id, ballotformpaper_id, vbfp_current, vbfp_date) VALUES(?, ?, 1, NOW())");
						insertStatement.setInt(1, voter.databaseID);
						insertStatement.setInt(2, serialNumber);
						insertStatement.execute();
						
						//Return an updated Voter
						return getVoterFromDatabaseID(voter.databaseID);
						
					} else {
						
						//The form should not be assigned
						return null;
					}

				} else {
					
					//This voter already has a form
					return null;
					
				}
				

			} else {
				
				//For some reason could not count in the database
				return null;
				
			}

		} catch (SQLException ex) {
			// TODO Auto-generated catch block
			ex.printStackTrace();
			return null;
		}
		
	}

	/**
	 * Cancels the form of a voter
	 */
	public Voter cancelFormForVoter(Voter voter) throws RemoteException {

		try {
			
	        //Create a statement and query database
			Statement statement = this.bulletinBoard.connection.createStatement(ResultSet.TYPE_SCROLL_INSENSITIVE, ResultSet.CONCUR_READ_ONLY);
			ResultSet rsVoterBallotForms = statement.executeQuery("SELECT p.ballotformpaper_id, p.ballotformpaper_status, v.vbfp_id FROM voterballotformpapers v, ballotformpapers p WHERE v.ballotformpaper_id = p.ballotformpaper_id AND v.voter_id = " + voter.databaseID + "");

			//Create update statements
			PreparedStatement ballotFormPaperUpdateStatement = this.bulletinBoard.connection.prepareStatement("UPDATE ballotformpapers SET ballotformpaper_status = 'CANCELLED', ballotformpaper_statuschangedate = NOW() WHERE ballotformpaper_id = ?");
			PreparedStatement ballotFormPaperStatusInsertStatement = this.bulletinBoard.connection.prepareStatement("INSERT INTO ballotformpaperstatuschangelogs (ballotformpaper_id, ballotformpaper_oldstatus, bfpscl_date) VALUES(?, ?, NOW())");
			PreparedStatement ballotFormUpdateStatement = this.bulletinBoard.connection.prepareStatement("UPDATE ballotforms SET ballotform_status = 'CANCELLED', ballotform_statuschangedate = NOW() WHERE ballotform_serialno = ?");
			PreparedStatement voterBallotFormUpdateStatement = this.bulletinBoard.connection.prepareStatement("UPDATE voterballotformpapers SET vbfp_current = 0 WHERE vbfp_id = ?");

			//Go through each of these forms
			while(rsVoterBallotForms.next()) {

				int vbfp_id = rsVoterBallotForms.getInt("vbfp_id");
				System.out.println("Working on ballot paper id " + rsVoterBallotForms.getInt("ballotformpaper_id") + " with vbfp_id " + vbfp_id);
				
				//Insert into ballotformpaperstatuschangelogs
				ballotFormPaperStatusInsertStatement.setInt(1, rsVoterBallotForms.getInt("ballotformpaper_id"));
				ballotFormPaperStatusInsertStatement.setString(2, rsVoterBallotForms.getString("ballotformpaper_status"));
				ballotFormPaperStatusInsertStatement.execute();

				//Change ballot form paper status to CANCELLED
				ballotFormPaperUpdateStatement.setInt(1, rsVoterBallotForms.getInt("ballotformpaper_id"));
				ballotFormPaperUpdateStatement.execute();
				
				//Update ballot forms to CANCELLED
				Statement ballotFormStatement = this.bulletinBoard.connection.createStatement(ResultSet.TYPE_SCROLL_INSENSITIVE, ResultSet.CONCUR_READ_ONLY);
				ResultSet rsBallotForms = ballotFormStatement.executeQuery("SELECT b.ballotform_serialno FROM ballotforms b, ballotformsinpapers i WHERE b.ballotform_serialno = i.ballotform_id AND i.ballotformpaper_id = " + rsVoterBallotForms.getInt("ballotformpaper_id"));
				while(rsBallotForms.next()) {
					
					ballotFormUpdateStatement.setInt(1, rsBallotForms.getInt("ballotform_serialno"));
					ballotFormUpdateStatement.execute();
					
				}
				
				//Set the VoterBallotFormPaper to not current
				voterBallotFormUpdateStatement.setInt(1, vbfp_id);
				voterBallotFormUpdateStatement.execute();
				
			}

			//Return new Voter
			return getVoterFromDatabaseID(voter.databaseID);
			
		} catch (SQLException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
			return null;
		}

	}

	/**
	 * Looks up a voter from a URN
	 */
	public Voter voterLookup(String urn) throws RemoteException {
		
		try {
			
	        //Create a statement
			Statement statement = this.bulletinBoard.connection.createStatement(ResultSet.TYPE_SCROLL_INSENSITIVE, ResultSet.CONCUR_READ_ONLY);

			//Query database
			ResultSet rsVoter = statement.executeQuery("SELECT voter_id FROM voters WHERE voter_urn = '" + urn + "'");
			
			//Check if there was something
			if(rsVoter.next()) {
				
				//Return new Voter object
				return getVoterFromDatabaseID(rsVoter.getInt(("voter_id")));
				
			} else {
				
				//No voter with this URN was found
				return null;
				
			}

		} catch (SQLException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
			return null;
		}

	}
	
	/**
	 * Selects a Voter object from the database using the primary key
	 * 
	 * @param id
	 * @return
	 */
	private Voter getVoterFromDatabaseID(int id) {

		try {
			
	        //Create a statement
			Statement statement = this.bulletinBoard.connection.createStatement(ResultSet.TYPE_SCROLL_INSENSITIVE, ResultSet.CONCUR_READ_ONLY);
	
			//Query database
			ResultSet rsVoter = statement.executeQuery("SELECT * FROM voters WHERE voter_id = '" + id + "'");
			
			//Check if there was something
			if(rsVoter.next()) {
				
				//Create a new voter object
				Voter voter = new Voter(rsVoter.getInt("voter_id"), rsVoter.getString("voter_urn"), rsVoter.getString("voter_name"), rsVoter.getDate("voter_dob"));
				
				//Check if there are any ballot forms assigned to this voter
				ResultSet rsBallotForm = statement.executeQuery("SELECT v.vbfp_date, p.ballotformpaper_id, p.ballotformpaper_status, p.ballotformpaper_statuschangedate, IF(v.vbfp_current = 1, true, false) AS current FROM voterballotformpapers v, ballotformpapers p WHERE v.ballotformpaper_id = p.ballotformpaper_id AND voter_id = " + rsVoter.getInt("voter_id") + "");
				
				//If there are any ballot forms then add these to the voter object
				while(rsBallotForm.next()) {
					voter.addBallotForm(new VoterBallotFormPaper(rsBallotForm.getInt("ballotformpaper_id"), rsBallotForm.getString("ballotformpaper_status"), rsBallotForm.getTimestamp("vbfp_date"), rsBallotForm.getBoolean("current")));
				}
				
				//We are done, return the voter
				return voter;
				
			} else {
				
				//No voter with this URN was found
				return null;
				
			}

		} catch (SQLException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
			return null;
		}

	}
	
	/**
	 * Allows a bulletin board to cancel a vote if there has been a read error.
	 * This always returns a receipt of type Receipt.ERROR_VOTE_MALFORMED
	 * 
	 * @param vote The vote representing the ballot form to cancel
	 * @return A cancellation receipt
	 */
	public Receipt cancelForm(Vote vote) {
		
		try {
			
			/*
			 * CHECK THE SIGNATURE OF THE VOTING BOOTH 
			 */
			
			//Get the booth public key
			Booth currentBooth = this.bulletinBoard.getBoothFromID(vote.boothID);
			if(currentBooth == null) {
				return new Receipt(Receipt.ERROR_NOT_A_BOOTH, vote.id, vote.signedHash, vote.signedHash, vote.permutations, "No booth with this ID is loaded", this.bulletinBoard.privateKey);
			}
	
	        //Test the signature
	        if(!vote.checkSignature(currentBooth.publicKey)) {
	        	return new Receipt(Receipt.ERROR_NOT_A_BOOTH, vote.id, vote.signedHash, vote.signedHash, vote.permutations, "Signature check failed.", this.bulletinBoard.privateKey);
	        }
		        
	        /*
	         * Get the ballot form paper and the associated ballot forms
	         */

	        //Create a statement
			Statement statement = this.bulletinBoard.connection.createStatement(ResultSet.TYPE_SCROLL_INSENSITIVE, ResultSet.CONCUR_READ_ONLY);
	
			//Query database
			ResultSet rsBallotFormPaper = statement.executeQuery("SELECT * FROM ballotformpapers WHERE ballotformpaper_id = " + vote.id);
			
			//Check if there is a ballot form with this ID in the database - if not, throw InvalidBallotFormException
			if(!rsBallotFormPaper.next()) {
				return new Receipt(Receipt.ERROR_INVALID_BALLOT_FORM, vote.id, vote.signedHash, vote.signedHash, vote.permutations, "No ballot form paper with this ID in the database.", this.bulletinBoard.privateKey);
			}
			
			//Check the status of the ballot form
			String ballotFormPaperStatus = rsBallotFormPaper.getString("ballotformpaper_status");
			if(!ballotFormPaperStatus.equals(BallotForm.STATUS_AVAILABLE)) {
				return new Receipt(Receipt.ERROR_BALLOT_FORM_USED, vote.id, vote.signedHash, vote.signedHash, vote.permutations, "This ballot form is not available for submission. Its status is: " + ballotFormPaperStatus, this.bulletinBoard.privateKey);
			}
			
			/*
			 * Store vars
			 */
			
			//The ballot form paper id
			int ballotFormPaperID = rsBallotFormPaper.getInt("ballotformpaper_id");

			//Deserialise the hash
			ObjectInputStream ois = new ObjectInputStream(new BufferedInputStream(rsBallotFormPaper.getBinaryStream("ballotformpaper_hash")));
			byte[] ballotFormHash = (byte[])ois.readObject();
			//System.out.println("Hash on the ballot form: " + HexConstructor.byteArrayToHexString(ballotFormHash));

			/*
			 * CHECK THAT THE HASH AND SIGNATURE CORRESPOND WITH THE POSTED VALUES
			 */
			
			//Unsign the signed hash from the ballot form 
			byte[] unsignedHash = BallotFormPaper.removeHashSignature(vote.signedHash, this.bulletinBoard.administratorPublicKey);
			//System.out.println("        The signed hash: " + HexConstructor.byteArrayToHexString(vote.signedHash));
			//System.out.println("      The unsigned hash: " + HexConstructor.byteArrayToHexString(unsignedHash));
			//System.out.println("             comparison: " + HexConstructor.byteArrayToHexString(unsignedHash).compareTo(HexConstructor.byteArrayToHexString(ballotFormHash)));

			//Check that the hash where the signature has been removed is the same as the hash in the form
			if(HexConstructor.byteArrayToHexString(unsignedHash).compareTo(HexConstructor.byteArrayToHexString(ballotFormHash)) != 0) {
				return new Receipt(Receipt.ERROR_INVALID_HASH, vote.id, unsignedHash, vote.signedHash, vote.permutations, "Hash check failed.", this.bulletinBoard.privateKey);
			}
			
			//Serialize the vote object to store in the database
			ByteArrayOutputStream baos = new ByteArrayOutputStream();
		    ObjectOutputStream oout = new ObjectOutputStream(baos);
		    oout.writeObject(vote);
		    oout.close();

			//Mark the ballot form paper as CANCELLATION_IN_PROGRESS in the database
			PreparedStatement updateBallotFormPaperStatusStatement = this.bulletinBoard.connection.prepareStatement("UPDATE ballotformpapers SET ballotformpaper_status = ?, ballotformpaper_statuschangedate = NOW(), vote_object = ? WHERE ballotformpaper_id = ?");
			updateBallotFormPaperStatusStatement.setString(1, "CANCELLATION_IN_PRGS");
			updateBallotFormPaperStatusStatement.setBytes(2, baos.toByteArray());
			updateBallotFormPaperStatusStatement.setInt(3, ballotFormPaperID);
			updateBallotFormPaperStatusStatement.execute();

	        /*
	         * All is good now, proceed to posting the supplied ballot forms
	         */

			//Query database for the associated ballot forms
			ResultSet rsBallotForms = statement.executeQuery("SELECT f.* FROM ballotforms f, ballotformsinpapers i WHERE f.ballotform_serialno = i.ballotform_id AND i.ballotformpaper_id = " + ballotFormPaperID + " AND ballotform_status = 'AVAILABLE' ORDER BY i.position ASC");

			//Check the number of ballot forms
			rsBallotForms.last();
			int numberOfBallotForms = rsBallotForms.getRow();
			rsBallotForms.beforeFirst();

			//Check that there ARE ballot forms
			if(numberOfBallotForms == 0) {
				return new Receipt(Receipt.ERROR_INVALID_BALLOT_FORM, vote.id, unsignedHash, vote.signedHash, vote.permutations, "There were no ballot forms for this ballotformpaper.", this.bulletinBoard.privateKey);
			}

	        //Check that there are exactly the right number of votes
	        if(vote.permutations.size() != numberOfBallotForms) {
	        	return new Receipt(Receipt.ERROR_INVALID_BALLOT_FORM, vote.id, unsignedHash, vote.signedHash, vote.permutations, "The vote had " + vote.permutations.size() + " permutations but there are " + numberOfBallotForms + " ballot forms.", this.bulletinBoard.privateKey);
	        }

	        //Get an iterator for the permutations
	        Iterator permutationIterator = vote.permutations.iterator();
	        
	        //Go through all the forms and update them
	        while(rsBallotForms.next()) {
	        	
	        	//The permutation for this ballot form
	        	CharacterPermutation currentPermutation = (CharacterPermutation)permutationIterator.next();
	        	
				//De-serialise the BallotForm object from the database
				ObjectInputStream deserialisedBallotForm = new ObjectInputStream(new BufferedInputStream(rsBallotForms.getBinaryStream("ballotform_object")));
				BallotForm currentBallotForm = (BallotForm)deserialisedBallotForm.readObject();

				//Get the current election
				Election currentElection = this.bulletinBoard.getElectionFromID(currentBallotForm.votingForm.signedOnion.raceInfo.election);
				if(currentElection == null) {
					return new Receipt(Receipt.ERROR_INVALID_BALLOT_FORM, vote.id, unsignedHash, vote.signedHash, vote.permutations, "The election in the ballot form does not exist.", this.bulletinBoard.privateKey);
				}
				
				//Check if this election is currently accepting ballots
				if(!currentElection.isAcceptingVotes()) {
					return new Receipt(Receipt.ERROR_INVALID_BALLOT_FORM, vote.id, unsignedHash, vote.signedHash, vote.permutations, "This election is currently not accepting ballots.", this.bulletinBoard.privateKey);
				}
				
				//Get the current race
				Race currentRace = currentElection.getRaceFromID(currentBallotForm.votingForm.signedOnion.raceInfo.race);
				if(currentRace == null) {
					return new Receipt(Receipt.ERROR_INVALID_BALLOT_FORM, vote.id, unsignedHash, vote.signedHash, vote.permutations, "The race in the ballot form does not exist.", this.bulletinBoard.privateKey);
				}
				
				//Check if the permutations are of similar length
				if(!currentPermutation.testEqualNumberOfCandidates(currentRace.getBaseOrderPermutation())) {
					return new Receipt(Receipt.ERROR_INVALID_BALLOT_FORM, vote.id, unsignedHash, vote.signedHash, vote.permutations, "The voter's choice (" + currentPermutation.permutation.length + ") does not correspond to the number of candidates in this race (" + currentRace.getBaseOrderPermutation().permutation.length + "," + currentRace.candidates.size() + "). Election " + currentElection.electionID + " race " + currentRace.raceID + "(" + currentBallotForm.votingForm.signedOnion.raceInfo.race + ")" , this.bulletinBoard.privateKey);
				}
				
				//Set the Permutation on the VotingForm to the one received
				currentBallotForm.setVote(currentPermutation);
				
				//Set the status in the VotingForm to CANCELLED
				currentBallotForm.votingForm.status = "CANCELLED";
				
				//Re-serialise the BallotForm object
				baos = new ByteArrayOutputStream();
			    oout = new ObjectOutputStream(baos);
			    oout.writeObject(currentBallotForm);
			    oout.close();
				
				//Store the BallotForm in the database and change the status in the database to CANCELLED
				//and store the boothID against the form as well as the status change date
			    //TODO: This should update in a batch that may be rolled back!!
				PreparedStatement updateStatement = this.bulletinBoard.connection.prepareStatement("UPDATE ballotforms SET ballotform_status = ?, booth_id = ?, ballotform_object = ?, ballotform_statuschangedate = NOW() WHERE ballotform_serialno = ?");
				updateStatement.setString(1, "CANCELLED");
				updateStatement.setInt(2, vote.boothID);
				updateStatement.setBytes(3, baos.toByteArray());
				updateStatement.setInt(4, currentBallotForm.serialNo);
				updateStatement.execute();
				
				//Increment the number of votes cast
				currentBooth.incrementBallotCount();
				currentRace.incrementBallotCount();
	        	
	        }
			
			/*
			 * The vote was successfully posted!!
			 */
	        
			//Mark the ballot form paper as voted in the database
			updateBallotFormPaperStatusStatement = this.bulletinBoard.connection.prepareStatement("UPDATE ballotformpapers SET ballotformpaper_status = ?, ballotformpaper_statuschangedate = NOW() WHERE ballotformpaper_id = ?");
			updateBallotFormPaperStatusStatement.setString(1, "CANCELLED");
			updateBallotFormPaperStatusStatement.setInt(2, ballotFormPaperID);
			updateBallotFormPaperStatusStatement.execute();

	        //Return a receipt
			return new Receipt(Receipt.ERROR_VOTE_MALFORMED, vote.id, unsignedHash, vote.signedHash, vote.permutations, this.bulletinBoard.privateKey);
			
			
		} catch (InvalidKeyException e) {
			return new Receipt(Receipt.ERROR_NOT_A_BOOTH, vote.id, vote.signedHash, vote.signedHash, vote.permutations, "InvalidKeyException: " + e.getMessage(), this.bulletinBoard.privateKey);
		} catch (SQLException e) {
			return new Receipt(Receipt.ERROR_DATABASE_PROBLEM, vote.id, vote.signedHash, vote.signedHash, vote.permutations, "SQLException: " + e.getMessage(), this.bulletinBoard.privateKey);
		} catch (IOException e) {
			return new Receipt(Receipt.ERROR_INTERNAL_BULLETIN_BOARD_PROBLEM, vote.id, vote.signedHash, vote.signedHash, vote.permutations, "IOException: " + e.getMessage(), this.bulletinBoard.privateKey);
		} catch (ClassNotFoundException e) {
			return new Receipt(Receipt.ERROR_INTERNAL_BULLETIN_BOARD_PROBLEM, vote.id, vote.signedHash, vote.signedHash, vote.permutations, "ClassNotFoundException: " + e.getMessage(), this.bulletinBoard.privateKey);
		}

	}

	public boolean identifyTeller(String tellerName, String tellerServerName, String tellerServerAddress, byte[] tellerSignature) {

		//Get the teller
		Teller currentTeller = this.bulletinBoard.getTellerByName(tellerName);
		
		//Check if we found anything
		if(currentTeller != null) {

			//Check that an identification nonce is present
			if(currentTeller.identificationNonce != null) {

				try {

					//Re-create the checksum
					Signature signature = Signature.getInstance("SHA1withRSA");
					signature.initVerify(currentTeller.publicKey);
					
					//Add teller name to digest
					signature.update(tellerName.getBytes("ISO-8859-1"));
					
					//Add teller server name to digest
					signature.update(tellerServerName.getBytes("ISO-8859-1"));
					
					//Add teller address to digest
					signature.update(tellerServerAddress.getBytes("ISO-8859-1"));
					
					//Add nonce to digest
					signature.update(currentTeller.identificationNonce);
					
					//Check that the signature is correct
					if(signature.verify(tellerSignature)) {

						//Update the teller's name in mamory
						currentTeller.serverName = tellerServerName;
						
						//Update the teller's address in memory
						currentTeller.address = tellerServerAddress;
						
						//TODO: Update the teller's address in database
			
						//Remove the identification nonce so it cannot be reused
						currentTeller.identificationNonce = null;
			
						//The identification was successful
						return true;
						
					} else {
						
						System.out.println("The signature was not verified.");
						return false;
						
					}
					
				} catch (NoSuchAlgorithmException e) {
					
					e.printStackTrace();
					return false;
					
				} catch (UnsupportedEncodingException e) {

					e.printStackTrace();
					return false;
					
				} catch (InvalidKeyException e) {
					
					e.printStackTrace();
					return false;
					
				} catch (SignatureException e) {

					e.printStackTrace();
					return false;
					
				}
				
			} else {
				
				System.out.println("There is no identification nonce for this teller.");
				return false;
				
			}

		} else {
			
			//No teller with this name exists
			System.out.println("No teller with this name exists");
			return false;
			
		}
		
	}


	public byte[] identifyTellerGetNonce(String tellerName) {

		//Get the teller
		Teller currentTeller = this.bulletinBoard.getTellerByName(tellerName);
		
		//Check if we found anything
		if(currentTeller != null) {

			//Create a random nonce
			Random random = new Random();
			byte[] nonce = new byte[1000];
			random.nextBytes(nonce);
			
			//Store the nonce against the teller
			currentTeller.identificationNonce = nonce;
			
			//Return the nonce
			return nonce;

		} else {
			
			//No teller with this name exists
			return null;
			
		}
		
	}
	
}
