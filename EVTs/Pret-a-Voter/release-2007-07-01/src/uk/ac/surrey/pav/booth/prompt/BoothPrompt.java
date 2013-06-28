package uk.ac.surrey.pav.booth.prompt;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.ObjectInputStream;
import java.rmi.Naming;
import java.rmi.NotBoundException;
import java.rmi.RMISecurityManager;
import java.security.InvalidKeyException;
import java.security.PrivateKey;
import java.util.Properties;

import uk.ac.surrey.pav.ballotform.CharacterPermutation;
import uk.ac.surrey.pav.ballotform.Receipt;
import uk.ac.surrey.pav.ballotform.Vote;
import uk.ac.surrey.pav.bulletinboard.BulletinBoardInterface;
import uk.ac.surrey.pav.common.HexConstructor;

/**
 * This is used to submit a vote from a comma separated value string that is
 * created by some other OCR software.
 * 
 * @author David Lundin
 *
 */
public class BoothPrompt {

	/**
	 * @param args ballotID,signed hash,123,123,123,123,...
	 */
	public static void main(String[] args) {

		try {

			//Read from standard input
			String cvsline;
			BufferedReader in = new BufferedReader(new InputStreamReader(System.in));
			
			//System.out.println("Hi, I'm Boothprompt!");
			if((cvsline = in.readLine()) != null && cvsline.length() > 0) {

    			//System.out.println("Read a line.");

				//Let's load a security manager
				if(System.getSecurityManager() == null) {
					System.setSecurityManager(new RMISecurityManager());
				}
				
				//Load settings
				Properties props = new Properties();
                props.load(Class.class.getResourceAsStream("/uk/ac/surrey/pav/booth/prompt/boothprompt.prop"));
    			//System.out.println("Properties loaded.");
                
				//The ID of the entity
				int boothID = Integer.parseInt(props.getProperty("id"));

				//Load Booth private key from file
				ObjectInputStream objectIn = new ObjectInputStream(Class.class.getResourceAsStream("/uk/ac/surrey/pav/booth/prompt/Booth_private_key.ppk"));
				PrivateKey privateBoothKey = (PrivateKey)objectIn.readObject();

				//Load Audit private key from file
				objectIn = new ObjectInputStream(Class.class.getResourceAsStream("/uk/ac/surrey/pav/booth/prompt/Auditmachine_private_key.ppk"));
				PrivateKey privateAuditmachineKey = (PrivateKey)objectIn.readObject();

				//Split the input args into: command, serial number, signedHash, vote, vote, vote, vote, vote, vote, vote, msg, msg, msg, msg, msg, msg, msg
				String[] commands = cvsline.split(",");
				
				//System.out.println("There were " + commands.length + " commands.");
				
				//Check that there are the correct number of things coming in
				if(commands.length >= 4) {

					//Store the command
					int commandNumber = Integer.parseInt(commands[0]);
					//System.out.println("commandNumber: " + commandNumber);
					
					//Start outputting
					StringBuffer output = new StringBuffer();

					//If this is a proper ballot form (10) then proceed, otherwise just output
					if(commandNumber == 10 || commandNumber == 11) {

						//Get the ballot form id number
						int ballotID = Integer.parseInt(commands[1]);
						//System.out.println("ballotID: " + ballotID);

						//Get the signed hash
						byte[] signedHash = HexConstructor.hexStringToByteArray(commands[2]);
						
						//The number of votes in this vote
						int numberOfVotes = Integer.parseInt(commands[3]);
						//System.out.println("numberOfVotes: " + numberOfVotes);

						//Create the Vote object
						Vote vote = new Vote(ballotID, signedHash, boothID);
	
						//Add all the votes
						for(int x = 4; x < numberOfVotes + 4 && x < commands.length; x++) {
								
							//Add the vote
							vote.addVoteFromCharArray(commands[x].toCharArray());
								
						}
						
						//Count how many are actual votes
						int voteCount = 0;
						for(int x = 0; x < vote.permutations.size(); x++) {
							if(((CharacterPermutation)vote.permutations.get(x)).getNumberOfChoices() > 0) {
								voteCount++;
							}
						}
						//System.out.println("voteCount: " + voteCount);
						
						//Connect to the web bulletin board
						BulletinBoardInterface remoteBulletinBoard = (BulletinBoardInterface)Naming.lookup("rmi://" + props.getProperty("wbburl") + "/" + props.getProperty("wbbname"));

						//The resulting receipt
						Receipt receipt = null;
						
						if(commandNumber == 10) {
							//This is a proper vote that we are going to submit

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

						} else {
							//This is a "cancellation vote". It is cancelling because it doesn't make sense

							//Sign the Vote object
							vote.sign(privateBoothKey);
							
							//Invoke postBallot() on the web bulletin board
							receipt = remoteBulletinBoard.cancelForm(vote);

						}
						
						//Output the receipt
						output.append(receipt.toCSV() + ",");
						
						//The character length of the first 10 commands
						int commandLength = 0;
						for(int x = 0; x < numberOfVotes + 4 && x < commands.length; x++) {
							//Add the length of each of the commands
							commandLength += commands[x].length() + 1;
						}

						//If there is anything in the input string beyond this length then output this
						if(cvsline.length() > commandLength) {
							output.append(cvsline.substring(commandLength));
						}

					} else {
						
						//This error is pointless to send to the server
						output.append(cvsline.substring(commands[0].length() + 1));
						output.append(Receipt.ERROR_SCANNING_PROBLEM + ",");
						
					}
					
					//Print output to standard out
					System.out.println(output.toString());
					
					//Exits with exit code
					System.exit(0);

				} else {
					
					System.err.println("Invalid number of things to process (" + commands.length + ")");
				}
				
			} else {
				
				System.err.println("Invalid number of arguments.");
				
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
