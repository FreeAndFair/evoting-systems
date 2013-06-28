package uk.ac.surrey.pav.misc;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileOutputStream;
import java.io.ObjectOutputStream;
import java.security.KeyPair;
import java.security.KeyPairGenerator;
import java.security.PublicKey;
import java.sql.Connection;
import java.sql.DriverManager;
import java.sql.PreparedStatement;
import java.util.ArrayList;

import uk.ac.surrey.pav.ballotform.BallotForm;
import uk.ac.surrey.pav.ballotform.Permutation;
import uk.ac.surrey.pav.common.HexConstructor;

public class TestEntityCreator {

	/**
	 * @param args
	 */
	public static void main(String[] args) {
		
		try {
			
			/*
			 * CREATE THE CONNECTION TO THE DATABASE
			 * 
			 */
			
			//Load the database connection driver
			Class.forName ("com.mysql.jdbc.Driver");
	
			//Make the connection
			Connection connection = DriverManager.getConnection("jdbc:mysql://localhost/pretavoter", "root", "");

			/*
			 * Generating elections, races and candidates
			 */

			//Delete
			PreparedStatement delete = connection.prepareStatement("DELETE FROM elections");
			delete.execute();
			delete = connection.prepareStatement("DELETE FROM races");
			delete.execute();
			delete = connection.prepareStatement("DELETE FROM candidates");
			delete.execute();
			delete = connection.prepareStatement("DELETE FROM candidateraces");
			delete.execute();

			//Statements
			PreparedStatement electionStatement = connection.prepareStatement("INSERT INTO elections (election_id, election_name, election_startdate, election_enddate) VALUES (?, ?, '2007-02-26', '2007-03-05')");
			PreparedStatement raceStatement = connection.prepareStatement("INSERT INTO races (election_id, race_id, race_name) VALUES (?, ?, ?)");
			PreparedStatement candidateStatement = connection.prepareStatement("INSERT INTO candidates (candidate_id, candidate_name) VALUES (?, ?)");
			PreparedStatement candidateRaceStatement = connection.prepareStatement("INSERT INTO candidateraces (election_id, race_id, candidate_id) VALUES (?, ?, ?)");

			//Create 1 election
			for(int e=0; e<1; e++) {
				
				//Create the election
				electionStatement.setInt(1, e);
				electionStatement.setString(2, "Election " + (e + 1));
				electionStatement.execute();
				
				//Create 5 races
				for(int r=0; r<5; r++) {
					
					//Create the race
					raceStatement.setInt(1, e);
					raceStatement.setInt(2, r);
					raceStatement.setString(3, "Race " + (e + 1) + "-" + (r + 1));
					raceStatement.execute();
					
					//Create 5 candidates
					for(int c=0; c<5; c++) {
						
						//Create the candidate
						candidateStatement.setInt(1, (e*25) + (r*5) + c);
						candidateStatement.setString(2, "Candidate " + (e+1) + "-" + (r+1) + "-" + (c+1));
						candidateStatement.execute();
						
						//Insert the candidate in the race
						candidateRaceStatement.setInt(1, e);
						candidateRaceStatement.setInt(2, r);
						candidateRaceStatement.setInt(3, (e*25) + (r*5) + c);
						candidateRaceStatement.execute();
						
					}
				}
			}
			/*
			 * GENERATING TELLERS
			 */

			//Delete
			delete = connection.prepareStatement("DELETE FROM tellers");
			delete.execute();
			
			//Store the tellers' keys
			ArrayList tellerKeys = new ArrayList();
			
			//Create a statement
			PreparedStatement statement = connection.prepareStatement("INSERT INTO tellers (teller_id, teller_name, teller_ipaddress, teller_servername, teller_publickey, teller_sequencenumber) VALUES (?, ?, ?, ?, ?, ?)");

			//Create a number of objects, inject into database
			for(int x=0; x < 5; x++) {
				
				//Generate key pair
				KeyPairGenerator keyGen = KeyPairGenerator.getInstance("RSA");
				KeyPair tempRsaKey = keyGen.generateKeyPair();
				
				//Store the public key to use when creating ballot forms
				tellerKeys.add(tempRsaKey.getPublic());

				//Serialise the public key
				ByteArrayOutputStream baos = new ByteArrayOutputStream();
			    ObjectOutputStream oout = new ObjectOutputStream(baos);
			    oout.writeObject(tempRsaKey.getPublic());
			    oout.close();

			    //Store in the database
			    statement.setInt(1, x);
			    statement.setString(2, "Teller " + (x+1));
			    statement.setString(3, "127.0.0.1");
			    statement.setString(4, "Teller" + (x+1));
			    statement.setBytes(5, baos.toByteArray());
			    statement.setInt(6, x);
			    statement.execute();
			    
			    //Serialise the private key and store in file
			    File outFile = new File("C:/PrivateKeys/teller" + (x+1) + ".ppk");
			    ObjectOutputStream objectOut = new ObjectOutputStream(new FileOutputStream(outFile));
			    objectOut.writeObject(tempRsaKey.getPrivate());

			}
			
			statement.close();

			/*
			 * GENERATING BOOTHS
			 */

			//Delete
			delete = connection.prepareStatement("DELETE FROM booths");
			delete.execute();

			//Create a statement
			statement = connection.prepareStatement("INSERT INTO booths (booth_id, booth_name, booth_publickey) VALUES (?, ?, ?)");	

			//Create a number of objects, inject into database
			for(int x=0; x < 5; x++) {
				
				//Generate key pair
				KeyPairGenerator keyGen = KeyPairGenerator.getInstance("RSA");
				KeyPair tempRsaKey = keyGen.generateKeyPair();

				//Serialise public key
				ByteArrayOutputStream baos = new ByteArrayOutputStream();
			    ObjectOutputStream oout = new ObjectOutputStream(baos);
			    oout.writeObject(tempRsaKey.getPublic());
			    oout.close();

			    //Store in database
			    statement.setInt(1, x);
			    statement.setString(2, "Booth number " + (x+1));
			    statement.setBytes(3, baos.toByteArray());
			    statement.execute();

			    //Serialise the private key and store in file
			    File outFile = new File("C:/PrivateKeys/booth" + x + ".ppk");
			    ObjectOutputStream objectOut = new ObjectOutputStream(new FileOutputStream(outFile));
			    objectOut.writeObject(tempRsaKey.getPrivate());

			}
			
			statement.close();

			/*
			 * GENERATING AUDIT MACHINES
			 */

			//Delete
			delete = connection.prepareStatement("DELETE FROM auditmachines");
			delete.execute();

			//Create a statement
			statement = connection.prepareStatement("INSERT INTO auditmachines (auditmachine_id, auditmachine_name, auditmachine_publickey) VALUES (?, ?, ?)");	

			//Create a number of objects, inject into database
			for(int x=0; x < 5; x++) {
				
				//Generate key pair
				KeyPairGenerator keyGen = KeyPairGenerator.getInstance("RSA");
				KeyPair tempRsaKey = keyGen.generateKeyPair();

				//Serialise public key
				ByteArrayOutputStream baos = new ByteArrayOutputStream();
			    ObjectOutputStream oout = new ObjectOutputStream(baos);
			    oout.writeObject(tempRsaKey.getPublic());
			    oout.close();

			    //Store in database
			    statement.setInt(1, x);
			    statement.setString(2, "Audit machine " + (x+1));
			    statement.setBytes(3, baos.toByteArray());
			    statement.execute();
			    
			    //Serialise the private key and store in file
			    File outFile = new File("C:/PrivateKeys/auditmachine" + x + ".ppk");
			    ObjectOutputStream objectOut = new ObjectOutputStream(new FileOutputStream(outFile));
			    objectOut.writeObject(tempRsaKey.getPrivate());

			}
			
			statement.close();
			
			/*
			 * GENERATE BALLOT FORMS
			 */
			
			//Delete
			delete = connection.prepareStatement("DELETE FROM ballotforms");
			delete.execute();

			delete = connection.prepareStatement("DELETE FROM receipts");
			delete.execute();

			//Create a statement
			statement = connection.prepareStatement("INSERT INTO ballotforms (ballotform_serialno, ballotform_status, election_id, race_id, ballotform_object) VALUES (?, 'VOTED', ?, ?, ?)");	

			for(int e=0; e<1; e++) {
				for(int r=0; r<5; r++) {
					for(int f=0; f<1000; f++) {
					
						//New ballot form
						BallotForm newForm = new BallotForm((e*5000) + (r*1000) + f, 5, e, r);
						
						//Add layers to onion
						for(int k=0; k<tellerKeys.size(); k++) {
							newForm.addLayerToOnion((PublicKey)tellerKeys.get(k));
							newForm.addLayerToOnion((PublicKey)tellerKeys.get(k));
						}
						
						//Insert vote
						//newForm.setVote(new Permutation(5, "This is random"));
						
						//Serialise
						ByteArrayOutputStream baos = new ByteArrayOutputStream();
					    ObjectOutputStream oout = new ObjectOutputStream(baos);
					    oout.writeObject(newForm);
					    oout.close();
					    
					    //Insert
					    statement.setInt(1, (e*5000) + (r*1000) + f);
					    statement.setInt(2, e);
					    statement.setInt(3, r);
					    statement.setBytes(4, baos.toByteArray());
					    
					    statement.execute();

					}
				}
			}

		} catch (Exception e) {
			
			e.printStackTrace();
			
		}
	}

}
