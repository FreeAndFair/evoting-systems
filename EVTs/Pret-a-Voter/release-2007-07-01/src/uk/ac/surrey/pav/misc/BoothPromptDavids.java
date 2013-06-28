package uk.ac.surrey.pav.misc;

import java.io.FileInputStream;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.rmi.Naming;
import java.rmi.NotBoundException;
import java.security.InvalidKeyException;
import java.security.PrivateKey;

import uk.ac.surrey.pav.ballotform.CharacterPermutation;
import uk.ac.surrey.pav.ballotform.Receipt;
import uk.ac.surrey.pav.ballotform.Vote;
import uk.ac.surrey.pav.bulletinboard.BulletinBoardInterface;
import uk.ac.surrey.pav.common.HexConstructor;
import uk.ac.surrey.pav.common.interfaces.CSVable;

public class BoothPromptDavids {

	/**
	 * @param args
	 */
	public static void main(String[] args) {
		// TODO Auto-generated method stub

		try {

			if(args.length == 1) {

				//The ID of the entity
				int boothID = 0;

				//Load Booth private key from file
				ObjectInputStream objectIn = new ObjectInputStream(new FileInputStream("C:/votecomp/votecomp/Booth1_private_key.ppk"));
				PrivateKey privateBoothKey = (PrivateKey)objectIn.readObject();

				//Load Audit private key from file
				objectIn = new ObjectInputStream(new FileInputStream("C:/votecomp/votecomp/Auditmachine1_private_key.ppk"));
				PrivateKey privateAuditmachineKey = (PrivateKey)objectIn.readObject();

				//Split the input args into: command, serial number, signedHash, vote, vote, vote, vote, vote, vote, vote, msg, msg, msg, msg, msg, msg, msg
				String[] commands = args[0].split(",");
				
				//System.out.println("There were " + commands.length + " commands.");
				
				//Check that there are the correct number of things coming in
				if(commands.length >= 3) {

					//Store the command
					int commandNumber = Integer.parseInt(commands[0]);
					
					//Start outputting
					StringBuffer output = new StringBuffer();

					//If this is a proper ballot form (10) then proceed, otherwise just output
					if(commandNumber == 10) {

						//Get the ballot form id number
						int ballotID = Integer.parseInt(commands[1]);
						
						//Get the signed hash
						byte[] signedHash = HexConstructor.hexStringToByteArray(commands[2]);
						
						//Create the Vote object
						Vote vote = new Vote(ballotID, signedHash, boothID);
	
						//Add all the votes
						if(commands.length >= 4) {
							for(int x = 3; x <= 9 && x < commands.length; x++) {
								
								//Add the vote
								vote.addVoteFromCharArray(commands[x].toCharArray());
								
							}
						}
						
						//Count how many are actual votes
						int voteCount = 0;
						for(int x = 0; x < vote.permutations.size(); x++) {
							if(((CharacterPermutation)vote.permutations.get(x)).getNumberOfChoices() > 0) {
								voteCount++;
							}
						}
						
						//Connect to the web bulletin board
						BulletinBoardInterface remoteBulletinBoard = (BulletinBoardInterface)Naming.lookup("rmi://127.0.0.1/Bulletinboard");

						//The resulting receipt
						Receipt receipt = null;
						
						//Check how many votes are included in this request
						if(voteCount >= 1) {
							//This is a proper vote

							//Sign the Vote object
							vote.sign(privateBoothKey);
							
							//Invoke postBallot() on the web bulletin board
							receipt = remoteBulletinBoard.postBallot(vote);

						} else {
							//This is an audit request

							//Sign the Vote object
							vote.sign(privateAuditmachineKey);
							
							//Invoke postBallot() on the web bulletin board
							receipt = remoteBulletinBoard.auditForm(vote);

						}
						
						//Output the receipt
						output.append(receipt.toCSV() + ",");

					} else {
						
						//Simply output what we have and so forth
						output.append(Receipt.ERROR_VOTE_MALFORMED + ",");
						for(int x = 1; x < commands.length; x++) {
							output.append(commands[x] + ",");
						}
						
					}
					
					//Print output to standard out
					System.out.println(output.toString());
					
					//Exits with exit code
					System.exit(0);

				} else {
					
					System.out.println("Invalid number of things to process (" + commands.length + ")");
				}
				
			} else {
				
				System.out.println("Invalid number of arguments.");
				
			}

		} catch(IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (ClassNotFoundException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (InvalidKeyException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (NotBoundException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}

	}

}
