package uk.ac.surrey.pav.audit;

import java.io.BufferedInputStream;
import java.io.ObjectInputStream;
import java.math.BigInteger;
import java.security.MessageDigest;
import java.security.PublicKey;
import java.sql.Connection;
import java.sql.DriverManager;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;

import javax.swing.JProgressBar;

import uk.ac.surrey.pav.ballotform.BallotForm;
import uk.ac.surrey.pav.ballotform.Onion;
import uk.ac.surrey.pav.ballotform.Permutation;
import uk.ac.surrey.pav.common.HexConstructor;

/**
 * Performs the audit on the database
 * 
 * @author David Lundin
 *
 */
public class Auditor {
	
	/**
	 * Settings
	 */
	private AuditorSettings settings;
	
	/**
	 * Database connection
	 */
	private Connection connection;
		
	/**
	 * The number of parts in the total process
	 */
	private int progressTotalNumberOfParts = 0;
	
	/**
	 * The current part number
	 */
	private int progressCurrentPartNumber = 0;
	
	/**
	 * The table that shows what has been done
	 */
	private AuditTableModel table;
	
	/**
	 * The progress bar of everything that is done
	 */
	private JProgressBar totalProgressBar;
	
	/**
	 * Progress bar for the current action
	 */
	private JProgressBar partProgressBar;
	
	/**
	 * Connects to the database
	 *
	 */
	public boolean connectToDatabase() {
		
		try {

			//Load the database connection driver
			Class.forName ("com.mysql.jdbc.Driver");

			//Make the connection
			this.connection = DriverManager.getConnection(this.settings.getDatabaseConnectionString(), this.settings.getDatabaseUserName(), this.settings.getDatabasePassword());
			
			//Meta data about the database
			//ata dma = connection.getMetaData();
			
			//We've connected properly
			return true;

		} catch (ClassNotFoundException ex) {
			ex.printStackTrace();
			return false;
		} catch (SQLException ex) {
			ex.printStackTrace();
			return false;
		}

	}
	
	/**
	 * Constructor
	 * 
	 * @param settings
	 */
	public Auditor(AuditorSettings settings, AuditTableModel table, JProgressBar totalProgressBar, JProgressBar partProgressBar) {
		
		//Store the settings
		this.settings = settings;
		this.table = table;
		this.totalProgressBar = totalProgressBar;
		this.partProgressBar = partProgressBar;
		
	}

	public void auditAll() {
		
		//Set initial progress bars
		this.progressTotalNumberOfParts = 4;
		this.progressCurrentPartNumber = 0;
		
		//Connect to the database
		if(this.connectToDatabase()) {
			
			//Have connected to database
			this.addStatus("Database connection", "Connected");
			
			//Audit the audited ballot forms
			this.progressCurrentPartNumber++;
			this.auditBallotForms();
			
			//Audit the commitments
			this.progressCurrentPartNumber++;
			this.auditCommitments();
			
			//Audit the receipts
			this.progressCurrentPartNumber++;
			this.auditReceipts();
			
			//Audit the tally
			this.progressCurrentPartNumber++;
			this.auditTally();
			
		} else {
			
			//It was not possible to connect to the database
			this.progressCurrentPartNumber = this.progressTotalNumberOfParts;
			this.addStatus("Database connection", "Unable to connect");
			
		}
		
	}
	
	private void auditBallotForms() {
		
		try {

			//Create a statement and query
			Statement statement = connection.createStatement(ResultSet.TYPE_SCROLL_INSENSITIVE, ResultSet.CONCUR_READ_ONLY);
			ResultSet rsBallotForms = statement.executeQuery("SELECT DISTINCT ballotform_serialno FROM ballotformaudits ORDER BY ballotform_serialno");

			//A statement for getting the layers of the ballot forms
			Statement layerStatement = connection.createStatement(ResultSet.TYPE_SCROLL_INSENSITIVE, ResultSet.CONCUR_READ_ONLY);

			//Count the number of ballot forms
			rsBallotForms.last();
			int numberOfBallotForms = rsBallotForms.getRow();
			rsBallotForms.beforeFirst();

			//Set the progress bars to starting this
			this.addStatus("Audited ballot form check", "Started: " + numberOfBallotForms + " to check");

			//Iterate through all loaded ballot forms
			while(rsBallotForms.next()) {

				//Get the ballot form
				ResultSet rsBallotForm = layerStatement.executeQuery("SELECT * FROM ballotforms WHERE ballotform_serialno = " + rsBallotForms.getInt("ballotform_serialno") + "");
				
				//Check if we found the ballot form
				if(rsBallotForm.next()) {

					//Deserialise the ballot form object
					ObjectInputStream deserialisedBallotForm = new ObjectInputStream(new BufferedInputStream(rsBallotForm.getBinaryStream("ballotform_object")));
					BallotForm currentBallotForm = (BallotForm)deserialisedBallotForm.readObject();
					
					//Get a permutation in the canonical order
					Permutation currentPermutation = new Permutation(currentBallotForm.candidateList.permutation.length);
					
					//Get an "empty" onion
					Onion currentOnion = new Onion();
					
					//Get the layers of this ballot form
					ResultSet rsLayers = layerStatement.executeQuery("SELECT t.teller_publickey, a.audit_onion, a.audit_permutation, a.audit_germ FROM ballotformaudits a, tellers t WHERE a.teller_id = t.teller_id AND a.ballotform_serialno = " + rsBallotForms.getInt("ballotform_serialno") + " ORDER BY a.teller_id ASC, a.teller_batch DESC");
					
					//Go through the layers
					while(rsLayers.next()) {
						
						try {

							//Deserialise the germ
							byte[] layerGerm = rsLayers.getBytes("audit_germ");
							
							//Deserialise the onion
							ObjectInputStream deserialisedOnion = new ObjectInputStream(new BufferedInputStream(rsLayers.getBinaryStream("audit_onion")));
							Onion layerOnion = (Onion)deserialisedOnion.readObject();
							
							//Deserialise the permutation
							ObjectInputStream deserialisedPermutation = new ObjectInputStream(new BufferedInputStream(rsLayers.getBinaryStream("audit_permutation")));
							Permutation layerPermutation = (Permutation)deserialisedPermutation.readObject();

							//Deserialise the teller public key
							ObjectInputStream deserialisedKey = new ObjectInputStream(new BufferedInputStream(rsLayers.getBinaryStream("teller_publickey")));
							PublicKey layerPublicKey = (PublicKey)deserialisedKey.readObject();

							//Permute the layer according to what we got out of the layer
							currentPermutation.permute(layerPermutation);
							
							//Add a layer to the onion
							//TODO: Must stick the correct randomness into the layer!
							currentOnion.addLayer(layerPublicKey, layerPermutation);

						} catch (ClassCastException ex) {
							
							ex.printStackTrace();
							this.addStatus("Ballot form " + rsLayers.getInt("ballotform_serialno") + ", teller " + rsLayers.getInt("teller_id") + ", batch " + rsLayers.getInt("teller_batch"), "Unable to deserialise layer");

						}

					}
					
					//Check if the permutation we have now got matches the one in the form
					if(!this.comparePermutations(currentBallotForm.candidateList, currentPermutation)) {
						this.addStatus("Ballot form " + currentBallotForm.serialNo, "Candidate list check failure: " + currentBallotForm.candidateList.toString() + " ne " + currentPermutation.toString());
					}
					
					//Check if the onion hashes match
					if(!this.compareHashes(currentBallotForm.votingForm.signedOnion.onion.hash, currentOnion.hash)) {
						//this.addStatus("Ballot form " + currentBallotForm.serialNo, "Onion hash check failed");
					}
					
					//Set the progress bar
					this.setPartProgressBar(rsBallotForms.getRow(), numberOfBallotForms, "Checking audited ballot forms");

				} else {

					this.addStatus("Ballot form " + rsBallotForms.getInt("ballotform_serialno"), "Ballot form not found");

				}

			}

			//Set the progress bars to finished this
			this.addStatus("Audited ballot form check", "Finished");
			this.setPartProgressBar(numberOfBallotForms, numberOfBallotForms, "Checking audited ballot forms");

		} catch (Exception ex) {
			
			ex.printStackTrace();
			this.addStatus("Audited ballot form check", "Failed: " + ex.getMessage());
			
		}
		
	}
	
	private void auditCommitments() {

		try {

			//Create a statement and query
			Statement statement = connection.createStatement(ResultSet.TYPE_SCROLL_INSENSITIVE, ResultSet.CONCUR_READ_ONLY);
			ResultSet rsCommitments = statement.executeQuery("SELECT * FROM commitments");

			//Count the number of commitments
			rsCommitments.last();
			int numberOfCommitments = rsCommitments.getRow();
			rsCommitments.beforeFirst();
			
			//Set the progress bars to starting this
			this.addStatus("Checking teller commitments", "Started: " + numberOfCommitments + " to check");

			//Iterate through all commitments
			while(rsCommitments.next()) {
			
				//Create a digest
				MessageDigest md = MessageDigest.getInstance("SHA1");
				
				//Add the bulletinBoardNonce to the digest
				md.update(rsCommitments.getBytes("commitment_bulletinboard_nonce"));

				//Create the tellerNonce and add to digest
				md.update(rsCommitments.getBytes("commitment_teller_nonce"));
				
				//Create the bitmap and add to digest
				md.update(rsCommitments.getBytes("commitment_bitmap"));
				
				//Store the commitment
				if((new BigInteger(rsCommitments.getBytes("commitment_commitment"))) == (new BigInteger(md.digest()))) {
					
					//Ooooops, this commitment check failed
					this.addStatus("Commitment for election " + rsCommitments.getInt("election_id") + ", race " + rsCommitments.getInt("race_id") + ", teller " + rsCommitments.getInt("teller_id"), "Failed");
					
				}

				//Set the progress bar
				this.setPartProgressBar(rsCommitments.getRow(), numberOfCommitments, "Checking teller commitments");

			}
			
			//Set the progress bars to finished this
			this.addStatus("Checking teller commitments", "Finished");
			this.setPartProgressBar(numberOfCommitments, numberOfCommitments, "Checking teller commitments");

		} catch (Exception ex) {
			
			ex.printStackTrace();
			this.addStatus("Commitment check", "Failed: " + ex.getMessage());
			
		}

	}
	
	private void auditReceipts() {

		try {
			
			//Create a statement and query
			Statement statement = connection.createStatement(ResultSet.TYPE_SCROLL_INSENSITIVE, ResultSet.CONCUR_READ_ONLY);
			ResultSet rsReceipts = statement.executeQuery("SELECT * FROM ballotforms WHERE ballotform_status = 'VOTED'");

			//Count the number of commitments
			rsReceipts.last();
			int numberOfReceipts = rsReceipts.getRow();
			rsReceipts.beforeFirst();
			
			//Set the progress bars to starting this
			this.addStatus("Checking receipts", "Started: " + numberOfReceipts + " to check");
			
			//TODO: Load batches
			
			//TODO: Check receipts
			
			//Set the progress bars to finished this
			this.addStatus("Checking receipts", "Finished");
			this.setPartProgressBar(numberOfReceipts, numberOfReceipts, "Checking receipts");
			
		} catch (SQLException ex) {
			
			ex.printStackTrace();
			this.addStatus("Receipt check", "Failed: " + ex.getMessage());

		}


	}
	
	private void auditTally() {
		
		try {
			
			//Create a statement and query
			Statement statement = connection.createStatement(ResultSet.TYPE_SCROLL_INSENSITIVE, ResultSet.CONCUR_READ_ONLY);
			ResultSet rsTallies = statement.executeQuery("SELECT * FROM tallies GROUP BY election_id, race_id, tally_round");

			//Count the number of commitments
			rsTallies.last();
			int numberOfTallies = rsTallies.getRow();
			rsTallies.beforeFirst();
			
			//Set the progress bars to starting this
			this.addStatus("Checking tally", "Started: " + numberOfTallies + " to check");
			
			//TODO: Load batches
			
			//TODO: Check receipts
			
			//Set the progress bars to finished this
			this.addStatus("Checking tally", "Finished");
			this.setPartProgressBar(numberOfTallies, numberOfTallies, "Checking tally");
			
		} catch (SQLException ex) {
			
			ex.printStackTrace();
			this.addStatus("Tally check", "Failed: " + ex.getMessage());

		}
	}
	
	private void setPartProgressBar(int finished, int total, String description) {
		
		int partFinished = (int)(((float)finished / (float)total) * 100);
		this.partProgressBar.setValue(partFinished);
		this.partProgressBar.setString(description + " (" + partFinished + "%)");
		int totalFinished = (int)(((float)this.progressCurrentPartNumber / (float)this.progressTotalNumberOfParts) * 100);
		this.totalProgressBar.setValue(totalFinished);
		this.totalProgressBar.setString("Total progress (" + totalFinished + "%)");
		
	}
		
	private void addStatus(String action, String result) {
		
		this.table.addRow(action, result);
		
	}
	
	/**
	 * Compares two permutations
	 * 
	 * TODO: Move this to the Permutation.equals method
	 * 
	 * @param first
	 * @param second
	 * @return
	 */
	private boolean comparePermutations(Permutation first, Permutation second) {
		
		if(first.permutation.length != second.permutation.length) {
			//The permutations are of different length and so cannot be compared
			return false;
		}
		
		for(int x = 0; x < first.permutation.length; x++) {
			if(first.permutation[x] != second.permutation[x]) {
				//Found a digit which is not the same
				return false;
			}
		}
		
		//The check held
		return true;
		
	}
	
	/**
	 * Compares two hashes
	 * 
	 * TODO: Move to the BallotForm object
	 * 
	 * @param first
	 * @param second
	 * @return
	 */
	private boolean compareHashes(byte[] first, byte[] second) {
		
		System.out.println("First:  " + HexConstructor.byteArrayToHexString(first));
		System.out.println("Second: " + HexConstructor.byteArrayToHexString(second));
		
		if((new BigInteger(first)) == (new BigInteger(second))) {
			return true;
		} else {
			return false;
		}
		
	}

}
