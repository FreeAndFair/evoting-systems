/*
 * @(#)RTable.java
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
 * This is the results table
 */
package org.scantegrity.crypto.punchscan;

import java.util.Random;

/**
 * @author jay12701
 *
 */
public class RTable {
	RRow c_rTable[];
	Random c_rand; 
	
	public RTable(int p_numBallots, Random p_rand)
	{
		c_rTable = new RRow[p_numBallots];
		c_rand = p_rand; 
	}
	
	public void addResult(int p_ballotID, RRow p_result)
	{
		c_rTable[p_ballotID] = p_result; 
	}
	
	public void shuffle()
	{
		 // i is the number of items remaining to be shuffled.
	    for (int i = c_rTable.length; i > 1; i--) {
	        // Pick a random element to swap with the i-th element.
	        int j = c_rand.nextInt(i);  // 0 <= j <= i-1 (0-based array)
	        // Swap array elements.
	        RRow tmp = c_rTable[j];
	        c_rTable[j] = c_rTable[i-1];
	        c_rTable[i-1] = tmp;
	    }
	}
}
