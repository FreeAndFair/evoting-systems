package uk.ac.surrey.pav.misc;

import java.io.FileInputStream;
import java.io.ObjectInputStream;
import java.security.InvalidKeyException;
import java.security.KeyPair;

import uk.ac.surrey.pav.ballotform.BallotForm;
import uk.ac.surrey.pav.ballotform.Batch;
import uk.ac.surrey.pav.ballotform.Permutation;

/**
 * The Administrator module sets up the election.
 * 
 * @author David Lundin
 *
 */
public class Administrator {

	/**
	 * This runs the Administrator module.
	 * 
	 * @param args
	 */
	public static void main(String[] args) {
		
		//Set up the election
		int election = 0;
		int race = 0;
		
		int candidates = 5;
		
		//Set up a batch
		Batch batch = new Batch();
		
		//Set up 10 empty ballot forms
		for(int x = 0; x < 1; x++) {
			batch.addBallotForm(new BallotForm(x, candidates, election, race));
		}
		
		//Read in five key pairs
		KeyPair[] keyPairs = {null, null, null, null, null};
		try {
			for(int x = 1; x <= 5; x++) {
				FileInputStream fis = new FileInputStream("C:\\Documents and Settings\\Administrator\\My Documents\\key" + x + ".bin"); 
		        ObjectInputStream ois = new ObjectInputStream(fis); 
		        keyPairs[x-1] = (KeyPair) ois.readObject(); 
		        ois.close(); 
		        fis.close();
			}
		} catch (Exception e) {
			e.printStackTrace();
		}
		
		//Add five layers to the onions
		//For each key pair
		for(int x = 0; x < keyPairs.length; x++) {
			//For each ballot form
			for(int y = 0; y < batch.ballotForms.size(); y++) {
				//Add layer to the onion
				((BallotForm)batch.ballotForms.get(y)).addLayerToOnion(keyPairs[x].getPublic());
			}
		}
		
		//Add a vote to ballot form number 1...
		int[] choices = {0,1,2,3,4};
		((BallotForm)batch.ballotForms.get(0)).setVote(new Permutation(choices));
		
		//...and decrypt it
		//For each key pair
		for(int x = keyPairs.length - 1; x >= 0; x--) {
			//Remove the layer from the onion
			try {
				((BallotForm)batch.ballotForms.get(0)).removeLayerFromOnion(keyPairs[x].getPrivate());
			} catch (InvalidKeyException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}

	}

}
