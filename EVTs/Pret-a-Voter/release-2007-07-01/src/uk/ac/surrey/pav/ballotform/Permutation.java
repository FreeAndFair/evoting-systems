package uk.ac.surrey.pav.ballotform;

import java.io.IOException;
import java.io.Serializable;
import java.util.Random;

import sun.misc.BASE64Decoder;
import uk.ac.surrey.pav.common.interfaces.CSVable;

/**
 * Stores a permutation, either of the candidates
 * in the candidate list on a ballot form or the choices
 * of a voter on the encrypted receipt.
 * 
 * @author David Lundin
 * 
 */
public class Permutation implements Serializable, Cloneable, CSVable {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	
	/**
	 * Holds the permutation
	 */
	public int[] permutation;
	
	/**
	 * Apply a permutation to this permutation. This is simply
	 * achieved by moving the entries in this permutation into
	 * the order of the other permutation.
	 * 
	 * @param p	another permutation
	 */
	public void permute(Permutation p) {
		//Check the given permutation can be applied here
		if(p.permutation.length == this.permutation.length) {
			//Copy current values
			int[] currentPermutation = new int[this.permutation.length];
			System.arraycopy(this.permutation, 0, currentPermutation, 0, this.permutation.length);
			
			//Copy the permutation to apply
			int[] applyPermutation = new int[p.permutation.length];
			System.arraycopy(p.permutation, 0, applyPermutation, 0, p.permutation.length);
			
			//Go through all the values
			for(int x = this.permutation.length - 1; x >= 0; x--) {
				//Find the largest value
				int largest = -1;
				int largestPosition = 0;
				for(int y = 0; y < applyPermutation.length; y++) {
					if(applyPermutation[y] > largest) {
						//Store what is smallest
						largest = applyPermutation[y];
						largestPosition = y;
					}
				}

				//Some audit text
				//System.out.println("Largest is " + largest + " at " + largestPosition);
				
				//Move the value at the position of the largest here
				this.permutation[x] = currentPermutation[largestPosition];
				applyPermutation[largestPosition] = -1;
			}
		} else {
			System.err.println("The permutations are of different sizes (" + this.permutation.length + ":" + p.permutation.length + ") and cannot be applied to each other.");
		}
	}

	/**
	 * This is used to apply a permutation in reverse to this permutation.
	 * 
	 * @param p A permuation to apply to this.
	 */
	/*public void reverse(Permutation p) {
		//Check the given permutation can be applied here
		if(p.permutation.length == this.permutation.length) {
			//Copy current values
			int[] currentPermutation = new int[this.permutation.length];
			System.arraycopy(this.permutation, 0, currentPermutation, 0, this.permutation.length);
			
			//Go through all the values
			for(int x = 0; x < p.permutation.length; x++) {
				//Move the value to position with that index
				this.permutation[x] = currentPermutation[p.permutation[x]];
			}
		} else {
			System.err.println("The permutations are of different sizes (" + this.permutation.length + ":" + p.permutation.length + ") and cannot be applied to each other.");
		}
	}*/

	/**
	 * Sets up the canonical order of a specified number
	 * of candidates so that these may be shuffled
	 * in the process of creating the ballot form.
	 * 
	 * @param candidates	The number of candidates in this race
	 */
	public Permutation(int candidates) {
		//Creates new list of candidates
		this.permutation = new int[candidates];
		
		//Fill the list with the canonical order of the candidates
		for(int x = 0; x < this.permutation.length; x++) {
			this.permutation[x] = x;
		}
	}
	
	/**
	 * Sets up a permutation with a specified number of candidates
	 * in random order. The randomising of the candidates is done by
	 * drawing as many random numbers as there are candidates and
	 * using the descending order of these random numbers to order
	 * the candidates. 
	 * 
	 * @param candidates	The number of candidates in this race
	 * @param mode			Set to anything to invoke this constructor
	 */
	public Permutation(int candidates, String mode) {
		//Creates new list of candidates
		this.permutation = new int[candidates];

		//Set up a random generator
		Random rnd = new Random();
		
		//Assign a random value to each candidate,
		//all random values will be higher than the number of candidates
		for(int x = 0; x < this.permutation.length; x++) {
			int tempInt = rnd.nextInt();
			if(tempInt < 0) tempInt *= -1;
			this.permutation[x] = tempInt + candidates;
		}
		
		for(int x = 0; x < this.permutation.length; x++) {
			//Find the candidate with the highest random number
			int highest = 0;
			int highestPosition = 0;
			for(int y = 0; y < this.permutation.length; y++) {
				//Go through all values
				if(this.permutation[y] > highest) {
					//This value is higher than the others found, store
					highest = this.permutation[y];
					highestPosition = y;
				}
			}
			
			//Assign the position with the highest random value
			//the candidate with the lowest index
			this.permutation[highestPosition] = x;
		}
	}
	
	/**
	 * Create a set permutation, for example for storing a voter's choice.
	 * 
	 * @param intp An integer array representing the voter's choice
	 */
	public Permutation(int[] intp) {
		//Set up emtpy permutation
		this.permutation = new int[intp.length];
		
		//Store the permutation
		for(int x = 0; x < intp.length; x++) {
			this.permutation[x] = intp[x];
		}
	}
	
	/**
	 * Returns a string containing all the candidates, for example
	 * used when creating a CSV representation of BallotFormPaper objects
	 * 
	 * @return String representation of permutation
	 */
	public String getPermutationStringIncrementedByOne() {
		//Concatenate all
		String output = "";
		for(int x = 0; x < this.permutation.length; x++) {
			output += (this.permutation[x] + 1);
		}
		//Return the concatenated string
		return output;
	}
	
	/**
	 * Compare this with another permutation to check if they
	 * both have the same number of candidates
	 * 
	 * @param p A permutation to test against this
	 * @return Boolean true if the two permutations have the same number of candidates
	 */
	public boolean testEqualNumberOfCandidates(Permutation p) {
		
		if(this.permutation.length == p.permutation.length) {
			return true;
		} else {
			return false;
		}
		
	}
	
	/**
	 * Takes in an array of strings and sorts that array into
	 * the order indicated by the permutation. If, for example, the
	 * input string array contains the names of the candidates, these come out
	 * in the order indicated by the permutation.
	 * 
	 * @param sourceString String[] containing candidate names
	 * @return String[] containing same candidate names in the order indicated by the permutation
	 */
	public String[] shuffleString(String[] sourceString) {
		
		//Create a result string
		String[] resultString = new String[sourceString.length];
		
		/*
		 * Shuffle from source to result to represent this permutation
		 */
		
		int last = 999999999;
		
		for(int y=sourceString.length - 1; y>=0; y--) {
			//Find highest position
			int highest = -1;
			int highestPosition = 0;
			for(int x=0; x<sourceString.length; x++) {
				if(this.permutation[x] > highest && this.permutation[x] < last) {
					highest = this.permutation[x];
					highestPosition = x;
				}
			}
			resultString[y] = sourceString[highestPosition];
			last = this.permutation[highestPosition];
		}
		
		//Finished, return
		return resultString;
		
	}
	
	/**
	 * Clones the permutation object
	 * 
	 * @return New Permutation object
	 * @throws CloneNotSupportedException
	 */
	public Object clone() throws CloneNotSupportedException {
		super.clone();
		
		//Return new permutation
		return new Permutation(this.permutation);
	}
	
	/**
	 * Returns the permutation transposed, that is to say that the array
	 * contains the candidate IDs ranked rather than rankings in the order
	 * of the candidate list base order
	 * 
	 * @return A transposed integer array of the permutation
	 */
	public int[] getTransposedIntegerArray() {
		
		//Return array
		int[] result = new int[this.permutation.length];
		
		//Go through all and sort into new list
		for(int x=0; x<this.permutation.length; x++) {
			result[this.permutation[x]-1] = x;
		}
		
		//Done, return
		return result;
		
	}
	
	/**
	 * Returns CSV representation of the permutation
	 */
	public StringBuffer toCSV() {
		
		//The result
		StringBuffer result = new StringBuffer();
		
		//Add each digit
		for(int x = 0; x < this.permutation.length; x++) {
			
			//Add this digit
			result.append(this.permutation[x] + 1);
			
		}
		
		//Return the result
		return result;
		
	}
	
	/**
	 * Returns the bytes that represent the permutation
	 * 
	 * @return The bytes that represent the permutation
	 */
	public byte[] getBytes() {
		
		try {

			//A string buffer to hold the permutation
			StringBuffer buffer = new StringBuffer();
			
			//Add each digit
			for(int x = 0; x < this.permutation.length; x++) {
				buffer.append(this.permutation[x]);
				buffer.append("|");
			}
			
			//Create a byte[] by Base64 decoding
			BASE64Decoder decoder = new BASE64Decoder();
			return decoder.decodeBuffer(buffer.toString());
			
		} catch(IOException e) {
			
			e.printStackTrace();
			return null;
			
		}
		
	}
	
	/**
	 * Returns the permutation as a string
	 */
	public String toString() {
		StringBuffer result = new StringBuffer();
		for(int x = 0; x < this.permutation.length; x++) {
			result.append(this.permutation[x]);
			if(x < this.permutation.length - 1) {
				result.append("|");
			}
		}
		return result.toString();
	}

	
}
