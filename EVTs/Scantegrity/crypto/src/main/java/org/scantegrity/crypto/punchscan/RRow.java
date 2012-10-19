/*
 * @(#)RRow.java
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
 * This is a row in the results table
 */
package org.scantegrity.crypto.punchscan;

/**
 * @author jay12701
 *
 */
public class RRow {
	int c_results[]; 
	int c_ballotID; 
	
	public RRow(int p_ballotID)
	{
		c_ballotID = p_ballotID;
		c_results = null;
	}

	public void setResult(int[] p_results) {
		c_results = p_results;
	}

}
