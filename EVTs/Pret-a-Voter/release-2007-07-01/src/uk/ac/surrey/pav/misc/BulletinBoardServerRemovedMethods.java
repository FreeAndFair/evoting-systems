package uk.ac.surrey.pav.misc;

import java.io.BufferedInputStream;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutput;
import java.io.ObjectOutputStream;
import java.rmi.RemoteException;
import java.security.InvalidKeyException;
import java.security.NoSuchAlgorithmException;
import java.security.Signature;
import java.security.SignatureException;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;
import java.util.ArrayList;

import uk.ac.surrey.pav.ballotform.BallotForm;
import uk.ac.surrey.pav.ballotform.Onion;
import uk.ac.surrey.pav.ballotform.Permutation;
import uk.ac.surrey.pav.bulletinboard.entities.AuditMachine;
import uk.ac.surrey.pav.bulletinboard.entities.Booth;
import uk.ac.surrey.pav.bulletinboard.entities.Election;
import uk.ac.surrey.pav.bulletinboard.entities.Race;
import uk.ac.surrey.pav.bulletinboard.entities.Teller;
import uk.ac.surrey.pav.bulletinboard.exceptions.BulletinBoardMalfunctionException;
import uk.ac.surrey.pav.bulletinboard.exceptions.InvalidAuditMachineException;
import uk.ac.surrey.pav.bulletinboard.exceptions.InvalidBallotFormException;
import uk.ac.surrey.pav.bulletinboard.exceptions.InvalidBoothException;
import uk.ac.surrey.pav.bulletinboard.exceptions.InvalidElectionException;
import uk.ac.surrey.pav.bulletinboard.exceptions.TellerDownException;
import uk.ac.surrey.pav.bulletinboard.exceptions.TellerMalfunctionException;
import uk.ac.surrey.pav.bulletinboard.exceptions.UsedBallotFormException;

public class BulletinBoardServerRemovedMethods {

	/**
	 * Accepts the voter's choice from the booth and stores it in the database
	 * 
	 * @param serialNo		Serial number of the ballot form
	 * @param voterChoice	A Permutation object representing the voter's choice
	 * @param boothID		The ID number of the submitting booth
	 * @param signature		The booth's signature for the serialNo and voterChoice objects
	 * @return Boolean true if the ballot form is successfully posted
	 * @throws RemoteException
	 * @throws InvalidBoothException
	 * @throws BulletinBoardMalfunctionException
	 * @throws InvalidBallotFormException
	 * @throws UsedBallotFormException
	 */
	public boolean postIndividualBallot(int serialNo, Permutation voterChoice, int boothID, byte[] signature) throws RemoteException, InvalidBoothException, BulletinBoardMalfunctionException, InvalidBallotFormException, UsedBallotFormException, InvalidElectionException {

		/*
		 * Check signature to be from authenticated booth
		 * 
		 * Throws InvalidBoothException
		 */
		
		//Get the booth public key
		Booth currentBooth = this.bulletinBoard.getBoothFromID(boothID);
		if(currentBooth == null) {
			//No booth with this ID is loaded
			throw new InvalidBoothException("You are not a registered booth.");
		}

		try {
			
			//Create the signature object
			Signature testSignature = Signature.getInstance("SHA1withRSA");
			testSignature.initVerify(currentBooth.publicKey);
	
			//Add the ballot form serial number
			testSignature.update((serialNo + "").getBytes());
			
	        //Serialize the permutation
			ByteArrayOutputStream permutationBAOS = new ByteArrayOutputStream() ;
	        ObjectOutput permutationOO = new ObjectOutputStream(permutationBAOS) ;
	        permutationOO.writeObject(voterChoice);
	        permutationOO.close();
	        //Add to signature
	        testSignature.update(permutationBAOS.toByteArray());
	        
	        //Test the signature
	        if(!testSignature.verify(signature)) {
	        	throw new InvalidBoothException("The provided signature is invalid.");
	        }
	        
	        //All is good now, proceed to posting the supplied ballot form
	        
		} catch (NoSuchAlgorithmException e) {
			throw new BulletinBoardMalfunctionException(e, "Could not load the algorithm to check the signature.");
		} catch (InvalidKeyException e) {
			throw new BulletinBoardMalfunctionException(e, "The booth public key from the database is invalid.");
		} catch (SignatureException e) {
			throw new BulletinBoardMalfunctionException(e, "Signature exception when trying to verify signature.");
		} catch (IOException e) {
			throw new BulletinBoardMalfunctionException(e, "IOException when trying to verify signature.");
		}

		/*
		 * Get BallotForm object from database with this serial number,
		 * update it and store it again with the appropriate logs
		 * 
		 * Throws InvalidBallotFormException, UsedBallotFormException
		 */
		
		try {
			
			//Create a statement
			Statement statement = this.bulletinBoard.connection.createStatement(ResultSet.TYPE_SCROLL_INSENSITIVE, ResultSet.CONCUR_READ_ONLY);
	
			//Query database
			ResultSet rsBallotForm = statement.executeQuery("SELECT * FROM ballotforms WHERE ballotform_serialNo = " + serialNo);
			
			//Check if there is a ballot form with this ID in the database - if not, throw InvalidBallotFormException
			if(!rsBallotForm.next()) {
				throw new InvalidBallotFormException("The ballot form with the given ID could not be found in the database.");
			}
			
			//Check the status of the form - if not AVAILABLE throw UsedBallotFormException
			String ballotformStatus = rsBallotForm.getString("ballotform_status");
			if(!ballotformStatus.equals("AVAILABLE")) {
				throw new UsedBallotFormException("This ballot form has already been used or cancelled.");
			}
				
			//De-serialise the BallotForm object from the database
			ObjectInputStream deserialisedBallotForm = new ObjectInputStream(new BufferedInputStream(rsBallotForm.getBinaryStream("ballotform_object")));
			BallotForm currentBallotForm = (BallotForm)deserialisedBallotForm.readObject();
			
			/*
			 * Check if the Permutation received is accurate for this Race - if not throw InvalidBallotFormException
			 */
			
			//Get the current election
			Election currentElection = this.bulletinBoard.getElectionFromID(currentBallotForm.votingForm.signedOnion.raceInfo.election);
			if(currentElection == null) {
				throw new InvalidBallotFormException("The election in the ballot form does not exist.");
			}
			
			//Check if this election is currently accepting ballots
			if(!currentElection.isAcceptingVotes()) {
				throw new InvalidElectionException("This election is currently not accepting ballots.");
			}
			
			//Get the current race
			Race currentRace = currentElection.getRaceFromID(currentBallotForm.votingForm.signedOnion.raceInfo.race);
			if(currentRace == null) {
				throw new InvalidBallotFormException("The race in the ballot form does not exist.");
			}
			
			//Check if the permutations are of similar length
			if(!voterChoice.testEqualNumberOfCandidates(currentRace.getBaseOrderPermutation())) {
				throw new InvalidBallotFormException("The voter's choice does not correspond to the number of candidates in this race.");
			}
			
			/*
			 * Update the ballot form and save it
			 */
			
			//Set the Permutation on the VotingForm to the one received
			currentBallotForm.votingForm.vote = voterChoice;
			
			//Set the status in the VotingForm to VOTED
			currentBallotForm.votingForm.status = "VOTED";
			
			//Re-serialise the BallotForm object
			ByteArrayOutputStream baos = new ByteArrayOutputStream();
		    ObjectOutputStream oout = new ObjectOutputStream(baos);
		    oout.writeObject(currentBallotForm);
		    oout.close();
			
			//Store the BallotForm in the database and change the status in the database to VOTED
			//and store the boothID against the form as well as the status change date
			PreparedStatement updateStatement = this.bulletinBoard.connection.prepareStatement("UPDATE ballotforms SET ballotform_status = ?, booth_id = ?, ballotform_object = ?, ballotform_statuschangedate = NOW() WHERE ballotform_serialno = ?");
			updateStatement.setString(1, "VOTED");
			updateStatement.setInt(2, boothID);
			updateStatement.setBytes(3, baos.toByteArray());
			updateStatement.execute();
			
			//Increment the number of votes cast
			currentBooth.incrementBallotCount();
			currentRace.incrementBallotCount();
				
		} catch (SQLException e) {
			throw new BulletinBoardMalfunctionException(e, "There was a problem with the database when trying to find the ballot form.");
		} catch (IOException e) {
			throw new BulletinBoardMalfunctionException(e, "The ballot form in the database was malformed.");
		} catch (ClassNotFoundException e) {
			throw new BulletinBoardMalfunctionException(e, "The bulletin board does not have the correct code installed.");
		}
		
		//We have successfully cast a vote!!
		return true;
	}

	public String[] auditForm(int serialNo, int auditMachineID, byte[] signature) throws RemoteException, InvalidAuditMachineException, BulletinBoardMalfunctionException, InvalidBallotFormException, UsedBallotFormException, TellerDownException, TellerMalfunctionException {

		/*
		 * Check that the signature is from an authenticated audit machine
		 * 
		 * If not, throw InvalidAuditMachineException
		 */
		
		//Get the booth public key
		AuditMachine currentAuditMachine = this.bulletinBoard.getAuditMachineFromID(auditMachineID);
		if(currentAuditMachine == null) {
			//No booth with this ID is loaded
			throw new InvalidAuditMachineException("You are not a registered booth.");
		}

		try {
			
			//Create the signature object
			Signature testSignature = Signature.getInstance("SHA1withRSA");
			testSignature.initVerify(currentAuditMachine.publicKey);
	
			//Add the ballot form serial number
			testSignature.update((serialNo + "").getBytes());
			
	        //Test the signature
	        if(!testSignature.verify(signature)) {
	        	throw new InvalidAuditMachineException("The provided signature is invalid.");
	        }
	        
		} catch (NoSuchAlgorithmException e) {
			throw new BulletinBoardMalfunctionException(e, "Could not load the algorithm to check the signature.");
		} catch (InvalidKeyException e) {
			throw new BulletinBoardMalfunctionException(e, "The audit machine public key from the database is invalid.");
		} catch (SignatureException e) {
			throw new BulletinBoardMalfunctionException(e, "Signature exception when trying to verify signature.");
		}

		/*
		 * Check that the ballot form exists and that it has not been used
		 * and update the database to reflect that the ballot form has been audited
		 * 
		 * If ballot form already used, throw UsedBallotFormException
		 */

		//These things are used later
		Election currentElection;
		Race currentRace;
		BallotForm currentBallotForm;
		
		try {
			
			//Create a statement
			Statement statement = this.bulletinBoard.connection.createStatement(ResultSet.TYPE_SCROLL_INSENSITIVE, ResultSet.CONCUR_READ_ONLY);
	
			//Query database
			ResultSet rsBallotForm = statement.executeQuery("SELECT * FROM ballotforms WHERE ballotform_serialNo = " + serialNo);
			
			//Check if there is a ballot form with this ID in the database - if not, throw InvalidBallotFormException
			if(!rsBallotForm.next()) {
				throw new InvalidBallotFormException("A ballot form with the given serial number could not be found in the database.");
			}
			
			//Check the status of the form - if not AVAILABLE throw UsedBallotFormException
			String ballotformStatus = rsBallotForm.getString("ballotform_status");
			if(!ballotformStatus.equals("AVAILABLE")) {
				throw new UsedBallotFormException("This ballot form has already been used or cancelled.");
			}
			
			//De-serialise the BallotForm object from the database
			ObjectInputStream deserialisedBallotForm = new ObjectInputStream(new BufferedInputStream(rsBallotForm.getBinaryStream("ballotform_object")));
			currentBallotForm = (BallotForm)deserialisedBallotForm.readObject();

			/*
			 * Check that the ballot form is well-formed in that election and race exist
			 */
			
			//Get the current election
			currentElection = this.bulletinBoard.getElectionFromID(currentBallotForm.votingForm.signedOnion.raceInfo.election);
			if(currentElection == null) {
				throw new InvalidBallotFormException("The election in the ballot form does not exist.");
			}
			
			//Get the current race
			currentRace = currentElection.getRaceFromID(currentBallotForm.votingForm.signedOnion.raceInfo.race);
			if(currentRace == null) {
				throw new InvalidBallotFormException("The race in the ballot form does not exist.");
			}
			
			//System.out.println("Election " + currentElection.name + " race " + currentRace.name);

			//Set the status in the VotingForm to AUDITED
			currentBallotForm.votingForm.status = "AUDITED";
			
			//Re-serialise the BallotForm object
			ByteArrayOutputStream baos = new ByteArrayOutputStream();
		    ObjectOutputStream oout = new ObjectOutputStream(baos);
		    oout.writeObject(currentBallotForm);
		    oout.close();
			
			//Store the BallotForm in the database and change the status in the database to INAUDIT
			//and store the auditMachineID against the form as well as the status change date
			PreparedStatement updateStatement = this.bulletinBoard.connection.prepareStatement("UPDATE ballotforms SET ballotform_status = ?, booth_id = ?, ballotform_object = ?, ballotform_statuschangedate = NOW() WHERE ballotform_serialno = ?");
			updateStatement.setString(1, "INAUDIT");
			updateStatement.setInt(2, auditMachineID);
			updateStatement.setBytes(3, baos.toByteArray());
			updateStatement.setInt(4, serialNo);
			updateStatement.execute();
			
			//We have updated the database, increase the number of forms audited
			currentElection.incrementBallotAuditCount();
			currentAuditMachine.incrementBallotCount();
				
		} catch (SQLException e) {
			e.printStackTrace();
			throw new BulletinBoardMalfunctionException(e, "There was a problem with the database when trying to find the ballot form.");
		} catch (IOException e) {
			throw new BulletinBoardMalfunctionException(e, "The ballot form in the database was malformed.");
		} catch (ClassNotFoundException e) {
			throw new BulletinBoardMalfunctionException(e, "The bulletin board does not have the correct code installed.");
		}

		/*
		 * Get the base order permutation of this race
		 * and the current onion
		 */
		
		//Store a list of all the permutations
		ArrayList permutationList = new ArrayList();
		
		//Get the full onion
		Onion currentOnion = currentBallotForm.votingForm.signedOnion.onion;
		
		/*
		 * Pass the form to each teller and publish the result in the database
		 * while updating the permutation
		 * 
		 * If a teller does not respond throw TellerDownException
		 */

		try {
			
			//Statement for inserting audit info into database
			PreparedStatement insertAuditStatement = this.bulletinBoard.connection.prepareStatement("INSERT INTO ballotformaudits (ballotform_serialno, teller_id, teller_batch, audit_germ, audit_onion, audit_permutation) VALUES (?, ?, ?, ?, ?, ?)");
	
			//Go through all tellers IN THE REVERSE ORDER
			for(int x=this.bulletinBoard.getTellerCount()-1; x>=0; x--) {
				
				//Get reference to teller
				Teller currentTeller = this.bulletinBoard.getTeller(x);
				
				//Get something from the teller
				ArrayList result = currentTeller.reveal(currentOnion);
				
				//Check if we have a result
				if(result == null) {
					throw new TellerDownException("Teller " + currentTeller.tellerID + " did not return anything when queried.");
				}
				if(result.size() != 6) {
					throw new TellerDownException("Teller " + currentTeller.tellerID + " returned the wrong number of items.");
				}
	
				//Check that the result is what we expect
				if(!(	result.get(0) instanceof Permutation
						&& result.get(1) instanceof String
						&& result.get(2) instanceof Onion
						&& result.get(3) instanceof Permutation
						&& result.get(4) instanceof String
						&& result.get(5) instanceof Onion)) {
					throw new TellerMalfunctionException("The teller returned unknown data.");
				}
				
				//References to data
				Permutation firstPermutation = (Permutation)result.get(0);
				String firstGerm = (String)result.get(1);
				Onion firstOnion = (Onion)result.get(2);
				Permutation secondPermutation = (Permutation)result.get(3);
				String secondGerm = (String)result.get(4);
				Onion secondOnion = (Onion)result.get(5);
				
				//Store new onion
				currentOnion = secondOnion;
				
				/*
				 * POST THE AUDIT INFORMATION TO THE DATABASE
				 */
				
				//Stuff to use when serialising the objects
				ByteArrayOutputStream baos = new ByteArrayOutputStream();
			    ObjectOutputStream oout = new ObjectOutputStream(baos);

			    //THE FIRST LAYER
				insertAuditStatement.setInt(1, currentBallotForm.serialNo);
				insertAuditStatement.setInt(2, currentTeller.tellerID);
				insertAuditStatement.setInt(3, 0);
				insertAuditStatement.setString(4, firstGerm);
				
				//The onion
			    oout.writeObject(firstOnion);
				insertAuditStatement.setBytes(5, baos.toByteArray());
				
				//The permutation
			    oout.writeObject(firstPermutation);
				insertAuditStatement.setBytes(6, baos.toByteArray());
				
				//Post to database
				insertAuditStatement.execute();

			    //THE SECOND LAYER
				insertAuditStatement.setInt(1, currentBallotForm.serialNo);
				insertAuditStatement.setInt(2, currentTeller.tellerID);
				insertAuditStatement.setInt(3, 1);
				insertAuditStatement.setString(4, secondGerm);
				
				//The onion
			    oout.writeObject(secondOnion);
				insertAuditStatement.setBytes(5, baos.toByteArray());
				
				//The permutation
			    oout.writeObject(secondPermutation);
				insertAuditStatement.setBytes(6, baos.toByteArray());
				
				//Post to database
				insertAuditStatement.execute();

				//Close the output stream
			    oout.close();
			    baos.close();

				//Store this permutation for the recreation of the candidate list 
				permutationList.add(firstPermutation);
				permutationList.add(secondPermutation);
				
			}
		
		} catch (SQLException e) {
			throw new BulletinBoardMalfunctionException(e, "There was a problem with the database when trying to store audit information.");
		} catch (IOException e) {
			throw new BulletinBoardMalfunctionException(e, "There was an IO problem when trying to store audit information.");
		}
		
		/*
		 * Return the permutation
		 */

		//Get base order permutation as the initial permutation
		Permutation resultPermutation = currentRace.getBaseOrderPermutation();

		//Apply all the permutations in order
		for(int x=permutationList.size() - 1; x>0; x--) {
			resultPermutation.permute((Permutation)permutationList.get(x));
		}

		//Mark the ballot form as audited
		PreparedStatement updateStatement;
		try {
			updateStatement = this.bulletinBoard.connection.prepareStatement("UPDATE ballotforms SET ballotform_status = ?, ballotform_statuschangedate = NOW() WHERE ballotform_serialno = ?");
			updateStatement.setString(1, "AUDITED");
			updateStatement.setInt(2, serialNo);
			updateStatement.execute();
		} catch (SQLException e) {
			throw new BulletinBoardMalfunctionException(e, "There was a problem with the database when trying to update the status to audited.");
		}

		//TODO: Return plain text permutation rather than Permutation object
		return resultPermutation.shuffleString(currentRace.getCandidateNameList());
		
	}

}
