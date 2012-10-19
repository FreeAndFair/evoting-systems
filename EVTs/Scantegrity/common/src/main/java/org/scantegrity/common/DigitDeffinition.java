package org.scantegrity.common;
/**
 * The geometry of every decimal digit (0-9) in the Tenacity Hr192 Bold font. 
 * A 1 represents a black pixel and a 0 a white one. 
 * @author stefan
 *
 */
public class DigitDeffinition {

	static byte[][][] digits={
		{
			{0,1,1,1,1,0},
			{1,1,0,0,1,1},
			{1,1,0,1,1,1},
			{1,1,1,1,1,1},
			{1,1,1,0,1,1},
			{1,1,0,0,1,1},
			{0,1,1,1,1,0}
		},
		{
			{0,0,0,1,1,1},
			{1,1,1,1,1,1},
			{1,1,1,1,1,1},
			{0,0,1,1,1,1},
			{0,0,1,1,1,1},
			{0,0,1,1,1,1},
			{0,0,1,1,1,1},			
		},
		{
			{0,1,1,1,1,0},
			{1,1,0,0,1,1},
			{0,0,0,0,1,1},
			{0,0,0,1,1,0},
			{0,0,1,1,0,0},
			{0,1,1,0,0,0},
			{1,1,1,1,1,1}			
		},
		{
			{0,1,1,1,1,0},
			{1,1,0,0,1,1},
			{0,0,0,0,1,1},
			{0,0,1,1,1,0},
			{0,0,0,0,1,1},
			{1,1,0,0,1,1},
			{0,1,1,1,1,0}
		},
		{
			{0,0,0,1,1,0},
			{0,0,1,1,1,0},
			{0,1,1,1,1,0},
			{1,1,0,1,1,0},
			{1,1,1,1,1,1},
			{0,0,0,1,1,0},
			{0,0,0,1,1,0}			
		},
		{
			{1,1,1,1,1,1},
			{1,1,0,0,0,0},
			{1,1,1,1,1,0},
			{0,0,0,0,1,1},
			{0,0,0,0,1,1},
			{1,1,0,0,1,1},
			{0,1,1,1,1,0}			
		},
		{
			{0,1,1,1,1,0},
			{1,1,0,0,0,0},
			{1,1,1,1,1,0},
			{1,1,0,0,1,1},
			{1,1,0,0,1,1},
			{1,1,0,0,1,1},
			{0,1,1,1,1,0}
		},
		{
			{1,1,1,1,1,1},
			{0,0,0,0,1,1},
			{0,0,0,1,1,0},
			{0,0,0,1,1,0},
			{0,0,1,1,0,0},
			{0,0,1,1,0,0},
			{0,1,1,0,0,0}			
		},
		{
			{0,1,1,1,1,0},
			{1,1,0,0,1,1},
			{1,1,0,0,1,1},
			{0,1,1,1,1,0},
			{1,1,0,0,1,1},
			{1,1,0,0,1,1},
			{0,1,1,1,1,0},
		},
		{
			{0,1,1,1,1,0},
			{1,1,0,0,1,1},
			{1,1,0,0,1,1},
			{1,1,0,0,1,1},
			{0,1,1,1,1,1},
			{0,0,0,0,1,1},
			{0,1,1,1,1,0}			
		}
	};
	
	public byte[][] get(byte i) {
		return digits[i];
	}
	
	public int getDigitHeight() {
		return digits[0].length;
	}

	public int getDigitWidth() {
		return digits[0][0].length;
	}
	/**
	 * @return the hamming distances between all the digit difinitions
	 */	
	public int[][] allHamingDistances() {
		int[][] ret=new int[digits.length][digits.length];
		for (int d1=0;d1<ret.length;d1++){
			for (int d2=d1+1;d2<ret[d1].length;d2++) {
				ret[d1][d2]=hammingDistance(d1,d2);
				ret[d2][d1]=ret[d1][d2];
				System.out.println("("+d1+","+d2+")="+ret[d1][d2]);
			}
		}
		return ret;
	}
	/**
	 * @param d1 between 0 and 9
	 * @param d2 between 0 and 9
	 * @return the hamming distance between two digits
	 */
	public int hammingDistance(byte[][] d1,byte[][] d2) {
		int ret = 0;
		for (int i=0;i<d1.length;i++)
			for (int j=0;j<d1[i].length;j++)
				ret+=Math.abs(d1[i][j]-d2[i][j]);				
		return ret;
	}
	
	/**
	 * Given a scanned digit, returns the digit that has the minimum hamming
	 * distance to one in the definition, if it is smaller then 0.35
	 * @param scannedDigit
	 * @return the digit that has the minimum hamming
	 * distance to one in the definition
	 * @throws Exception - if the closest valid digit is futher away then 0.35
	 */	
	public char minHammingDistance(byte[][] scannedDigit) throws Exception {
		int maxDistance = scannedDigit.length*scannedDigit[0].length;
		int min = maxDistance;
		char ret = '_';
		for (int d=0;d<digits.length;d++) {
			int currentDistance = hammingDistance(digits[d],scannedDigit);
			if (currentDistance<min) {
				min = currentDistance;
				ret = (char)((byte)d+'0');
			}
//			System.out.println(d+" "+currentDistance);
		}
		
		//TODO,some sanity check here. for example if scanned digit is close to two deffinition digits
//		System.out.println("detected "+ret+" min="+min);
		double threashhold = 0.35;
		if (min >= maxDistance*threashhold)
			throw new Exception("The digit seems to be "+ret+", but the hamming distance from the deffinition is "+min+" "+((min/(double)maxDistance)*100)+"% > "+threashhold);
		
		return ret;
	}
	
	/** 
	 * @param d1 between 0 and 9
	 * @param d2 between 0 and 9
	 * @return the hamming distance between two digits
	 */
	public int hammingDistance(int d1,int d2) {
		int ret = 0;
		for (int i=0;i<getDigitHeight();i++)
			for (int j=0;j<getDigitWidth();j++) {
				ret+=Math.abs(digits[d1][i][j]-digits[d2][i][j]);
			}
		return ret;
	}

	public static void main(String args[]) throws Exception {
		DigitDeffinition dd = new DigitDeffinition();
		dd.allHamingDistances();
		/*
		for (int i=0;i<dd.getNumberOfDigits();i++) {
			System.out.println(i+" "+dd.getDigitMap(i));
		}
		*/
	}

	public double getMaxDistance() {
		return 0;
	}

	public double getMinDistance() {
		return 0;
	}
}
