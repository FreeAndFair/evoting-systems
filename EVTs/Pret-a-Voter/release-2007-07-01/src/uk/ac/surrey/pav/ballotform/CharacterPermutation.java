package uk.ac.surrey.pav.ballotform;

import java.io.Serializable;

import uk.ac.surrey.pav.common.interfaces.CSVable;

/**
 * A character permutation represents the vote submitted by a voter.
 * It can hold any character in each position, which allows for any kind of election.
 * 
 * @author David Lundin
 *
 */
public class CharacterPermutation implements Serializable, Cloneable, CSVable {
	
	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	
	/**
	 * The permutation (i.e. voter's choice or something along those lines
	 * as represented by a number of chars
	 */
	public char[] permutation;
	
	/**
	 * Apply a permutation to this permutation. This is simply
	 * achieved by moving the entries in this permutation into
	 * the order of the other permutation.
	 * 
	 * @param p	another Permutation
	 */
	public void permute(Permutation p) {
		//Check the given permutation can be applied here
		if(p.permutation.length == this.permutation.length) {
			//Copy current values
			char[] currentPermutation = new char[this.permutation.length];
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
	public void reverse(Permutation p) {
		//Check the given permutation can be applied here
		if(p.permutation.length == this.permutation.length) {
			//Copy current values
			char[] currentPermutation = new char[this.permutation.length];
			System.arraycopy(this.permutation, 0, currentPermutation, 0, this.permutation.length);
			
			//Go through all the values
			for(int x = 0; x < p.permutation.length; x++) {
				//Move the value to position with that index
				this.permutation[x] = currentPermutation[p.permutation[x]];
			}
		} else {
			System.err.println("The permutations are of different sizes (" + this.permutation.length + ":" + p.permutation.length + ") and cannot be applied to each other.");
		}
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
	 * Clones the permutation object
	 * 
	 * @return New Permutation object
	 * @throws CloneNotSupportedException
	 */
	public Object clone() throws CloneNotSupportedException {
		super.clone();
		
		//Return new permutation
		return new CharacterPermutation(this.permutation);
	}

	public int getCandidateInChoiceNumber(int choiceNumber) {
		
		//A ranked list of candidates
		int[] choiceNumbers = new int[this.getNumberOfChoices()];
		
		//Go through the characters of the permutation
		for(int x = 0; x < this.permutation.length; x++) {
			
			switch(permutation[x]) {
			case 'x':
				choiceNumbers[0] = x;
				break;
			case '-':
			case 'o':
				break;
			default:
				choiceNumbers[Integer.parseInt(String.valueOf(permutation[x])) - 1] = x;
				break;
			}
			
		}
		
		//Okay, so return the one we are now after
		return choiceNumbers[choiceNumber];
		
	}
	
	/**
	 * Constructor
	 * 
	 * @param permutation
	 */
	public CharacterPermutation(char[] permutation) {
		this.permutation = permutation;
	}
	
	/**
	 * Returns the number of choices that this permutation
	 * represents. Here the characters - and o represent empty
	 * positions.
	 * 
	 * @return The number of choices represented here
	 */
	public int getNumberOfChoices() {
		int choiceCounter = 0;
		for(int x = 0; x < this.permutation.length; x++) {
			if(this.permutation[x] != '-' && this.permutation[x] != 'o') {
				choiceCounter++;
			}
		}
		return choiceCounter;
	}
	
	/**
	 * Returns the character permutation as a string
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

	/**
	 * Returns CSV representation of the permutation
	 */
	public StringBuffer toCSV() {
		StringBuffer result = new StringBuffer();
		for(int x = 0; x < this.permutation.length; x++) {
			result.append(this.permutation[x]);
		}
		return result;
	}

	
}
