/*
 * @(#)DTable.java
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
 * This is the DTable for the punchscan backend. 
 */
package org.scantegrity.crypto.punchscan;

import java.util.Random;

import org.scantegrity.crypto.Commitment;
import org.scantegrity.crypto.CommitmentScheme;


/**
 * @author jay12701
 *
 */
public class DTable {
	static final String DEFAULT_RAND_PROVIDER = "SUN";
	static final String DEFAULT_RAND_ALG = "SHA1PRNG";
	
	private DRow c_dTable[]; 
	private Random c_rand;
	
	public DTable(int p_numBallots, Random p_rand)
	{
		/*
		 * Each row in the table will be following: 
		 * 	Ballot ID, PermA, intermediate, PermB, Ptr to Results
		 */
		c_dTable = new DRow[p_numBallots];
		
		c_rand = p_rand;  
	}
	
	public void shuffle()
	{	
		 // i is the number of items remaining to be shuffled.
	    for (int i = c_dTable.length; i > 1; i--) {
	        // Pick a random element to swap with the i-th element.
	        int j = c_rand.nextInt(i);  // 0 <= j <= i-1 (0-based array)
	        // Swap array elements.
	        DRow tmp = c_dTable[j];
	        c_dTable[j] = c_dTable[i-1];
	        c_dTable[i-1] = tmp;
	    }	
	}

	public void add(DRow p_row, int p_ballotID) 
	{
		c_dTable[p_ballotID] = p_row; 
	}
	
	public DRow getRow(int index)
	{
		return c_dTable[index];
	}
	
	public void commitRows(CommitmentScheme p_cs)
	{
		for(int i = 0; i < c_dTable.length; i++)
		{
			try {
				c_dTable[i].setCommit(p_cs.commit(c_dTable[i].toByte()));
			} catch (Exception e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			} 
		}
	}
	
	public Commitment[] commitToRows(CommitmentScheme p_cs)
	{
		Commitment l_commits[] = new Commitment[c_dTable.length];
		
		for(int i = 0; i < c_dTable.length; i++)
		{
			try {
				l_commits[i] = p_cs.commit(c_dTable[i].toByte()); 
			} catch (Exception e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			} 
		}
		
		return l_commits; 
	}
	
	public Commitment[] commitCols(CommitmentScheme p_cs)
	{
		//we are commiting to two columns. 
		Commitment l_commits[] = new Commitment[2]; 
	
		String l_permA = ""; 
		String l_permB = "";  
		
		for(int i = 0; i < c_dTable.length; i++)
		{
			DRow l_row = c_dTable[i]; 
			
			l_permA += String.valueOf(l_row.getBallotID());
			l_permA += l_row.permToString(l_row.getPermA()); 
			l_permB += l_row.permToString(l_row.getPermB());
			l_permB += String.valueOf(l_row.getResPtr());
		}
		
		//commit to all the columns
		try {
			l_commits[0] = p_cs.commit(l_permA.getBytes()); 
			l_commits[1] = p_cs.commit(l_permB.getBytes());  
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
		return l_commits;
		
	}
}
