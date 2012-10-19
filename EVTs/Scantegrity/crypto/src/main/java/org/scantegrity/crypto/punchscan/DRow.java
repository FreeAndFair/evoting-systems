/*
 * @(#)DRow.java
 *  
 * Copyright (C) 2008 Scantegrity Project
 * 
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License along
 * with this program; if not, write to the Free Software Foundation, Inc.,
 * 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
 */

/**
 * This is a row in the DTable
 */
package org.scantegrity.crypto.punchscan;

import org.scantegrity.crypto.Commitment;

/**
 * @author jay12701
 *
 */
public class DRow {
	private int c_ballotID; 
	private int c_permA[][];
	private int c_intermediate[];
	private int c_permB[][];
	private RRow c_resPtr; 
	private Commitment c_commit; 
	
	public DRow(int p_ballotID, int p_permA[][], int p_permB[][])
	{
		c_ballotID = p_ballotID; 
		c_permA = p_permA; 
		c_permB = p_permB; 
		c_intermediate = null; 
		c_resPtr = new RRow(p_ballotID); 
		c_commit = null; 
	}
	
	public byte[] toByte()
	{
		String l_rowString = "";
		
		//convert ballot id to string
		l_rowString = String.valueOf(c_ballotID);
		
		//convert permA to string
		l_rowString += permToString(c_permA);
		
		//convert permB to string
		l_rowString += permToString(c_permB);
		
		//convert results ptr to string
		l_rowString += String.valueOf(c_resPtr); 
		
		//convert string to byte[]
		return l_rowString.getBytes();  
	}
	
	/**
	 * @return the c_ballotID
	 */
	public int getBallotID() {
		return c_ballotID;
	}

	/**
	 * @param cBallotID the c_ballotID to set
	 */
	public void setBallotID(int p_BallotID) {
		c_ballotID = p_BallotID;
	}

	/**
	 * @return the c_permA
	 */
	public int[][] getPermA() {
		return c_permA;
	}

	/**
	 * @param cPermA the c_permA to set
	 */
	public void setPermA(int[][] p_permA) {
		c_permA = p_permA;
	}

	/**
	 * @return the c_intermediate
	 */
	public int[] getIntermediate() {
		return c_intermediate;
	}

	/**
	 * @param cIntermediate the c_intermediate to set
	 */
	public void setIntermediate(int[] p_intermediate) {
		c_intermediate = p_intermediate;
	}

	/**
	 * @return the c_permB
	 */
	public int[][] getPermB() {
		return c_permB;
	}

	/**
	 * @param cPermB the c_permB to set
	 */
	public void setPermB(int[][] p_permB) {
		c_permB = p_permB;
	}

	/**
	 * @return the c_resPtr
	 */
	public RRow getResPtr() {
		return c_resPtr;
	}

	/**
	 * @param cResPtr the c_resPtr to set
	 */
	public void setResPtr(RRow p_resPtr) {
		c_resPtr = p_resPtr;
	}

	/**
	 * @return the c_commit
	 */
	public Commitment getCommit() {
		return c_commit;
	}

	/**
	 * @param cCommit the c_commit to set
	 */
	public void setCommit(Commitment p_commit) {
		c_commit = p_commit;
	}
	
	/* *******************************************************
	 * 
	 * Private Methods
	 * 
	 * *******************************************************/
	public String permToString(int p_perm[][])
	{
		String l_permString = ""; 
		
		for(int i = 0; i < p_perm.length; i++)
		{
			for(int j = 0; j < p_perm[i].length; i++)
			{
				l_permString += String.valueOf(p_perm[i][j]);
			}
		}
		
		return l_permString; 
	}

	public void sendResult(int[] p_results) 
	{
		int [] l_finalResults = new int[p_results.length];
		for(int i = 0; i < p_results.length; i++)
		{
			c_intermediate[i] = c_permA[i][p_results[i]];
			l_finalResults[i] = c_permB[i][c_intermediate[i]];
		}
		
		c_resPtr.setResult(l_finalResults); 
	}

}
