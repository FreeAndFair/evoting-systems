package uk.ac.surrey.pav.teller;

import java.math.BigInteger;
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
import java.util.Random;

import uk.ac.surrey.pav.ballotform.Onion;
import uk.ac.surrey.pav.ballotform.OnionLayer;
import uk.ac.surrey.pav.ballotform.PartialForm;
import uk.ac.surrey.pav.ballotform.TellerBatch;
import uk.ac.surrey.pav.ballotform.TellerInternalBatch;
import uk.ac.surrey.pav.ballotform.TellerInternalBatchRow;
import uk.ac.surrey.pav.bulletinboard.challenges.LeftRightGerm;
import uk.ac.surrey.pav.bulletinboard.challenges.NonceBitmapCouple;

/**
 * RMI server for the teller module
 * 
 * @author David Lundin
 *
 */
public class TellerServer extends UnicastRemoteObject implements TellerInterface {
	
	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	
	/**
	 * Settings
	 */
	private TellerSettings settings;

	/**
	 * Reveal an onion in the process of auditing a ballot form
	 * 
	 * @param onion
	 * @return A list of the two layer removed by this teller and their contents
	 * @throws RemoteException
	 * @throws InvalidKeyException
	 */
	public ArrayList reveal(Onion onion) throws RemoteException, InvalidKeyException {
		
		try {

			//Result variable
			ArrayList result = new ArrayList();
			
			/*
			 * Check if the onion has already been seen, if so stop
			 */
			
			//Query database
			//Statement statement = this.settings.databaseConnection.createStatement(ResultSet.TYPE_SCROLL_INSENSITIVE, ResultSet.CONCUR_READ_ONLY);
			//ResultSet testOnionStatement = statement.executeQuery("SELECT * FROM onions WHERE onion_hash = " + onion.getHashAsString());
			
			//Check if there is a similar onion in the database, if so die
			//if(!testOnionStatement.next()) {
				//TODO: Log why we are cancelling here
				//return null;
			//}
			
			/*
			 * Store the onion in the database
			 */

			//Prepare an insert statement
			PreparedStatement insertOnionStatement = this.settings.databaseConnection.prepareStatement("INSERT INTO onions (onion_hash, onion_date) VALUES (?, NOW())");
			
			//Add values
			insertOnionStatement.setString(1, onion.getHashAsString());
			
			//Execute
			insertOnionStatement.execute();

			/*
			 * Remove two layers
			 */
			
			//First layer
			OnionLayer topLayer = onion.removeLayer(settings.getPrivateKey());
			
			//Store the things to send back
			result.add(topLayer.permutation);
			result.add(topLayer.random);
			result.add((Onion)onion);

			//Add values
			insertOnionStatement.setString(1, onion.getHashAsString());
			
			//Execute
			insertOnionStatement.execute();

			//Second layer
			topLayer = onion.removeLayer(settings.getPrivateKey());
			
			//Store the things to send back
			result.add(topLayer.permutation);
			result.add(topLayer.random);
			result.add((Onion)onion);
			
			//Add values
			insertOnionStatement.setString(1, onion.getHashAsString());
			
			//Execute
			insertOnionStatement.execute();

			//Increment count of audited ballots
			this.settings.incrementBallotAuditCount();
			
			/*
			 * We are finished, return
			 */
			return result;

		} catch (Exception ex) {
			ex.printStackTrace();
			return null;
		}
		
	}

	/**
	 * Returns audit information for a given batch
	 * 
	 * @param election The election to be audited
	 * @param race The race to be audited
	 * @param batchID The batch to be audited
	 * @param mask The mask to be used to determined which links that are revealed
	 * @return A list of LeftRightGerm objects that represent the revealed links
	 * @throws RemoteException
	 */
	public ArrayList audit(int election, int race, int batchID, BigInteger mask) throws RemoteException {
		
		try {
		//TODO: STUB METHOD
		
			//Get internalBatchIDs for input, intermediate and output batches
			Statement statement = this.settings.databaseConnection.createStatement(ResultSet.TYPE_SCROLL_INSENSITIVE, ResultSet.CONCUR_READ_ONLY);
			ResultSet batchRS = statement.executeQuery("SELECT batch_internal_id FROM batches WHERE election_id = " + election + " AND race_id = " + race + " AND batch_id = " + batchID + " ORDER BY batch_column ASC");
			
			//Store zeros in the batch id vars first
			int inputBatchID = 0;
			int intermediateBatchID = 0;
			int outputBatchID = 0;
			
			//Now set to proper values
			if(batchRS.next()) {
				//Get input batch ID
				inputBatchID = batchRS.getInt("batch_internal_id");
			} else {
				System.out.println("There was no input batch!");
				return null;
			}
			if(batchRS.next()) {
				//Get input batch ID
				intermediateBatchID = batchRS.getInt("batch_internal_id");
			} else {
				System.out.println("There was no intermediate batch!");
				return null;
			}
			if(batchRS.next()) {
				//Get input batch ID
				outputBatchID = batchRS.getInt("batch_internal_id");
			} else {
				System.out.println("There was no output batch!");
				return null;
			}
			
			//Get the translations from database
			String query = "SELECT o2.onion_random AS input_random, o1.batch_sorted_place AS input_position, o2.batch_sorted_place AS intermediate_position, o3.batch_sorted_place AS output_position, o3.onion_random AS output_random FROM onions o1, onions o2, onions o3 WHERE o1.batch_sorted_place = o2.batch_place AND o2.batch_sorted_place = o3.batch_place AND o1.batch_id = " + inputBatchID + " AND o2.batch_id = " + intermediateBatchID + " AND o3.batch_id = " + outputBatchID + " ORDER BY intermediate_position ASC";
			System.out.println(query);
			ResultSet onionRS = statement.executeQuery(query);
			
			//Create a list of LeftRightGerms
			ArrayList result = new ArrayList();
			
			//Count which receipt we are dealing with
			int counter = 0;
			
			//Construct a LeftRightGerm for each and add to list
			while(onionRS.next()) {
				
				//TODO: Must return only as dictated by the mask!!!!
				if(mask.testBit(counter % mask.bitLength())) {
					//We are revealing the left link
					result.add(new LeftRightGerm(onionRS.getInt("input_position"), false, onionRS.getBytes("input_random")));
				} else {
					//We are revealing the right link
					result.add(new LeftRightGerm(false, onionRS.getInt("output_position"), onionRS.getBytes("output_random")));
				}
				
				//Increment the counter
				counter++;
			}
			
			//Return the list of LeftRightGerms
			return result;
			
		} catch (SQLException e) {
			
			e.printStackTrace();
			return null;
			
		}
		
	}
	
	/**
	 * Processes a batch of encrypted receipts
	 * 
	 * @param election The election to be processed
	 * @param race The race to be processed
	 * @param batchID The batch to be processed
	 * @param inputBatch The actual batch
	 * @return A list containing two new batches
	 * @throws RemoteException
	 * @throws InvalidKeyException
	 */
	public ArrayList processVote(int election, int race, int batchID, TellerBatch inputBatch) throws RemoteException, InvalidKeyException {
		
		try {
			
			//TODO: Check if a batch for this election, race, batchID exists
			
			//TODO: If the batch exists then stop
			
			/*
			 * INPUT BATCH
			 */
			
			//A statement to insert a batch in the db table
			PreparedStatement insertBatchStatement = this.settings.databaseConnection.prepareStatement("INSERT INTO batches (election_id, race_id, batch_id, batch_column, batch_date) VALUES (?, ?, ?, ?, NOW())");

			//Insert a batch for the input batch
			insertBatchStatement.setInt(1, election);
			insertBatchStatement.setInt(2, race);
			insertBatchStatement.setInt(3, batchID);
			insertBatchStatement.setInt(4, 0);
			insertBatchStatement.execute();
			
			//Store the internal batch id
			int internalBatchID = 0;
			ResultSet batchIDResultSet = insertBatchStatement.executeQuery("SELECT LAST_INSERT_ID()");
			if(batchIDResultSet.next()) {
				internalBatchID = batchIDResultSet.getInt(1);
			} else {
				//TODO: Die here!
			}

			//Prepare an insert statement
			PreparedStatement insertOnionStatement = this.settings.databaseConnection.prepareStatement("INSERT INTO onions (onion_hash, onion_random, batch_id, batch_place, batch_sorted_place, onion_date) VALUES (?, ?, ?, ?, ?, NOW())");
			
			//Go through all receipts in the input batch
			for(int x=0; x<inputBatch.ballotForms.size(); x++) {
				
				//TODO: Check if the onion has been seen before, if so stop 
				
				//Clone the partialform
				PartialForm tempPartialForm = (PartialForm)inputBatch.ballotForms.get(x);
				
				//Store in database
				insertOnionStatement.setString(1, tempPartialForm.onion.getHashAsString());
				insertOnionStatement.setBytes(2, null);
				insertOnionStatement.setInt(3, internalBatchID);
				insertOnionStatement.setInt(4, x);
				insertOnionStatement.setInt(5, x);
				insertOnionStatement.execute();

			}
			
			/*
			 * INPUT TO INTERMEDIATE BATCH
			 */
			
			//The intermediate batch
			TellerInternalBatch intermediateBatch = new TellerInternalBatch();

			//Insert a batch for the input batch
			insertBatchStatement.setInt(1, election);
			insertBatchStatement.setInt(2, race);
			insertBatchStatement.setInt(3, batchID);
			insertBatchStatement.setInt(4, 1);
			insertBatchStatement.execute();
			
			//Store the internal batch id
			internalBatchID = 0;
			batchIDResultSet = insertBatchStatement.executeQuery("SELECT LAST_INSERT_ID()");
			if(batchIDResultSet.next()) {
				internalBatchID = batchIDResultSet.getInt(1);
			} else {
				//TODO: Die here!
			}

			//Go through all receipts in the input batch
			for(int x=0; x<inputBatch.ballotForms.size(); x++) {
				
				//TODO: Check if the onion has been seen before, if so stop 
				
				//Clone the partialform
				PartialForm tempPartialForm = (PartialForm)((PartialForm)inputBatch.ballotForms.get(x)).clone();
				
				//Decrypt one layer into a TellerInternalBatchRow and store into table
				TellerInternalBatchRow tempRow = tempPartialForm.removeLayerIntoRow(this.settings.getPrivateKey());
				intermediateBatch.addRow(tempRow);

			}
			
			//Shuffle intermediate batch according to the onion value
			intermediateBatch.sort();
			
			//Store the intermediate batch in the database
			for(int x=0; x<intermediateBatch.getNumberOfRows(); x++) {

				//The current row
				TellerInternalBatchRow currentRow = intermediateBatch.getRow(x);
				
				//Store in database
				insertOnionStatement.setString(1, currentRow.partialForm.onion.getHashAsString());
				insertOnionStatement.setBytes(2, currentRow.random);
				insertOnionStatement.setInt(3, internalBatchID);
				insertOnionStatement.setInt(4, x);
				insertOnionStatement.setInt(5, currentRow.sortIndex);
				insertOnionStatement.execute();

			}

			/*
			 * INTERMEDIATE TO OUTPUT BATCH
			 */
			
			//The output batch
			TellerInternalBatch outputBatch = new TellerInternalBatch();
			
			//Insert a batch for the input batch
			insertBatchStatement.setInt(1, election);
			insertBatchStatement.setInt(2, race);
			insertBatchStatement.setInt(3, batchID);
			insertBatchStatement.setInt(4, 2);
			insertBatchStatement.execute();
			
			//Store the internal batch id
			internalBatchID = 0;
			batchIDResultSet = insertBatchStatement.executeQuery("SELECT LAST_INSERT_ID()");
			if(batchIDResultSet.next()) {
				internalBatchID = batchIDResultSet.getInt(1);
			} else {
				//TODO: Die here!
			}

			//Go through all the receipts in the intermediate batch
			for(int x=0; x<intermediateBatch.getNumberOfRows(); x++) {
				
				//Clone the partialform
				PartialForm tempPartialForm = (PartialForm)(intermediateBatch.getRow(x)).partialForm.clone();
				
				//Decrypt one layer into a TellerInternalBatchRow and store into table
				TellerInternalBatchRow tempRow = tempPartialForm.removeLayerIntoRow(this.settings.getPrivateKey());
				outputBatch.addRow(tempRow);
				
			}
			
			//Shuffle output batch by sorting according to the onion value
			outputBatch.sort();

			//Store output batch in database
			for(int x=0; x<outputBatch.getNumberOfRows(); x++) {

				//The current row
				TellerInternalBatchRow currentRow = outputBatch.getRow(x);
				
				//Store in database
				insertOnionStatement.setString(1, currentRow.partialForm.onion.getHashAsString());
				insertOnionStatement.setBytes(2, currentRow.random);
				insertOnionStatement.setInt(3, internalBatchID);
				insertOnionStatement.setInt(4, x);
				insertOnionStatement.setInt(5, currentRow.sortIndex);
				insertOnionStatement.execute();

			}

			//Increment count of processed batches
			this.settings.incrementBatchProcessCount();
			
			//Finished, return an ArrayList with two TellerBatches
			ArrayList result = new ArrayList();
			result.add(intermediateBatch.getTellerBatch());
			result.add(outputBatch.getTellerBatch());
			return result;
		
		} catch(CloneNotSupportedException ex) {
			
			//Could not clone for some reason
			ex.printStackTrace();
			return null;
			
		} catch (SQLException e) {
			
			// TODO Auto-generated catch block
			e.printStackTrace();
			return null;
			
		}
		
	}
	
	/**
	 * Constructor
	 * 
	 * @param settings TellerSettings object
	 */
	public TellerServer(TellerSettings settings) throws RemoteException {
		
		//Store the settings
		this.settings = settings;
		
		//Say I am alive
		this.settings.setStatus(true, "Running");
		
	}

	/**
	 * Commits to a seed value for a particular race to be audited
	 */
	public byte[] getCommitment(int election, int race, byte[] bulletinBoardNonce) throws RemoteException {
		
		try {

			//Check if a value exists already for the election+race, if so choose
			Statement statement = this.settings.databaseConnection.createStatement(ResultSet.TYPE_SCROLL_INSENSITIVE, ResultSet.CONCUR_READ_ONLY);
			ResultSet rsCommitment = statement.executeQuery("SELECT commitment_commitment FROM commitments WHERE election_id = " + election + " AND race_id = " + race);

			//If not exists, create a value and insert into database
			if(rsCommitment.next()) {
				
				//TODO: Check that the bulletinBoardNonce is the same as the one in the database, otherwise die
				
				//There already exists a value so return this
				return rsCommitment.getBytes("commitment_commitment");
				
			} else {
				
				//No value exists so create, insert and return

				//Create a digest
				MessageDigest md = MessageDigest.getInstance("SHA1");
				
				//Add the bulletinBoardNonce to the digest
				md.update(bulletinBoardNonce);

				//A random generator
				Random random = new Random();

				//Create the tellerNonce and add to digest
				byte[] tellerNonce = new byte[1000];
				random.nextBytes(tellerNonce);
				md.update(tellerNonce);
				
				//Create the bitmap and add to digest
				byte[] bitmap = new byte[16];
				random.nextBytes(bitmap);
				md.update(bitmap);
				
				//Store the commitment
				byte[] commitment = md.digest();
				
				//Store everything to the database
				PreparedStatement insertCommitmentStatement = this.settings.databaseConnection.prepareStatement("INSERT INTO commitments (election_id, race_id, commitment_bulletinboard_nonce, commitment_commitment, commitment_teller_nonce, commitment_bitmap, commitment_received) VALUES (?, ?, ?, ?, ?, ?, NOW())");
				insertCommitmentStatement.setInt(1, election);
				insertCommitmentStatement.setInt(2, race);
				insertCommitmentStatement.setBytes(3, bulletinBoardNonce);
				insertCommitmentStatement.setBytes(4, commitment);
				insertCommitmentStatement.setBytes(5, tellerNonce);
				insertCommitmentStatement.setBytes(6, bitmap);
				insertCommitmentStatement.execute();
				
				//Return the commitment value
				return commitment;

			}
			
		} catch (SQLException ex) {
			
			ex.printStackTrace();
			return null;
			
		} catch (NoSuchAlgorithmException ex) {
			
			ex.printStackTrace();
			return null;
			
		}
		
	}

	/**
	 * Reveals an audit seed value previously committed to
	 */
	public NonceBitmapCouple getValue(int election, int race) throws RemoteException {
		
		try {

			//Find the value in the database
			Statement statement = this.settings.databaseConnection.createStatement(ResultSet.TYPE_SCROLL_INSENSITIVE, ResultSet.CONCUR_READ_ONLY);
			ResultSet rsCommitment = statement.executeQuery("SELECT commitment_bulletinboard_nonce, commitment_teller_nonce, commitment_bitmap FROM commitments WHERE election_id = " + election + " AND race_id = " + race);

			if(rsCommitment.next()) {

				//Return the value
				return new NonceBitmapCouple(rsCommitment.getBytes(2), rsCommitment.getBytes(3));

			} else {
				
				//Bummer!
				System.out.println("Did not find anything in the database for election " + election + " and race " + race);
				return null;

			}

		} catch (SQLException e) {
			
			e.printStackTrace();
			return null;
			
		}
		
	}
	
	/**
	 * Allows the web bulletin board to connect to the teller over RMI
	 * and test the claimed identity of the teller server.
	 */
	public byte[] handShake(byte[] nonce) {
		
		try {

			//Set up a signature
			Signature signature = Signature.getInstance("SHA1withRSA");
			signature.initSign(this.settings.getPrivateKey());
			
			//Add the nonce to the signature
			signature.update(nonce);
			
			//Return the signature
			return signature.sign();

		} catch (NoSuchAlgorithmException e) {
			
			e.printStackTrace();
			return null;
			
		} catch (InvalidKeyException e) {
			
			e.printStackTrace();
			return null;

		} catch (SignatureException e) {
			
			e.printStackTrace();
			return null;

		}
		

	}
	
}
