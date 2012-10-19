/*
 * @(#)RandomBallotCreator.java
 *  
 * Copyright (C) 2008-2009 Scantegrity Project
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
package org.scantegrity.common;

import java.security.SecureRandom;
import java.util.TreeMap;

import org.scantegrity.common.Ballot;

/**
 * @author Richard Carback
 *
 */
public class RandomBallotCreator
{

	/**
	 * 
	 */
	public RandomBallotCreator()
	{
		// TODO Auto-generated constructor stub
	}

	/**
	 * @param args
	 */
	public static void main(String[] args)
	{
		// TODO Auto-generated method stub
		
	}

	public Ballot getBallot()
	{
		Ballot l_b = new Ballot();
		SecureRandom l_r = new SecureRandom();
		l_b.setId(Math.abs(l_r.nextInt()));
		l_b.setCounted(l_r.nextBoolean());
		
		int l_numraces = Math.abs(l_r.nextInt()%50);
		TreeMap<Integer, Integer[][]> l_bData = new TreeMap<Integer, Integer[][]>();
		for (int l_i = 0; l_i < l_numraces; l_i++)
		{
			int l_numcans = Math.abs(l_r.nextInt()%20);
			int l_numcols = Math.abs(l_r.nextInt()%10);
			Integer[][] l_rData = new Integer[l_numcans][l_numcols];
			for (int l_j = 0; l_j < l_numcans; l_j++)
			{
				for (int l_k = 0; l_k < l_numcols; l_k++)
				{
					l_rData[l_j][l_k] = Math.abs(l_r.nextInt());
				}
			}
			l_bData.put(Math.abs(l_r.nextInt()), l_rData);
		}
		l_b.setBallotData(l_bData);
		
		l_b.setBallotStyleID(Math.abs(l_r.nextInt()));
		l_b.addNote("Random Ballot Data");

		return l_b;
	}
	
}
