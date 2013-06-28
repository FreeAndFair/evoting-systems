package uk.ac.surrey.pav.bulletinboard.challenges;

import java.io.Serializable;

/**
 * Contains the left or right link and the germ, returned by the teller when challenged
 * 
 * @author David Lundin
 *
 */
public class LeftRightGerm implements Serializable {

	int left = -1;
	
	int right = -1;
	
	byte[] germ;
	
	public LeftRightGerm(int left, boolean test, byte[] germ) {
		
		this.left = left;
		this.germ = germ;
		
	}
	
	public LeftRightGerm(boolean test, int right, byte[] germ) {
		
		this.right = right;
		this.germ = germ;
		
	}

}
