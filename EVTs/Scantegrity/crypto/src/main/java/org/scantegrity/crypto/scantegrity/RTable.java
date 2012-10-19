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
package org.scantegrity.crypto.scantegrity;

import java.io.File;
import java.nio.ByteBuffer;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Random;

import org.scantegrity.crypto.CommitmentScheme;
// Amir editing
import org.scantegrity.crypto.FlatFileTable;

import table.FlatFileTable;




	public class RTable
	{
		ArrayList<Pointer<Integer, Integer>> c_pointersQ;
		ArrayList<Pointer<Integer, Integer>> c_pointersS;
		boolean[] c_flags;
		
		int c_ballots;
		int c_columns;
		
		Random c_rand;
		
		public RTable(int p_ballots, int p_columns, Random p_rand)
		{
			c_ballots = p_ballots;
			c_columns = p_columns;
			
			c_pointersQ = new ArrayList<Pointer<Integer, Integer>>();
			c_pointersS = new ArrayList<Pointer<Integer, Integer>>();
			
			c_flags = new boolean[p_ballots * p_columns];
			
			c_rand = p_rand;
			
			//Initialize R table with default values, grouped by columns so they can be permuted by the engine
			for( int x = 0; x < p_columns; x++ )
			{
				for( int y = 0; y < p_ballots; y++ )
				{
					c_pointersQ.add(new Pointer<Integer, Integer>(y, x));
					c_pointersS.add(new Pointer<Integer, Integer>(y, x));
				}
			}
			for( int x = 0; x < c_columns; x++ )
			{
				shuffleRange(x * c_ballots, (x+1) * c_ballots);
			}
		}
		
		//Switches column pointers when permuting rows in table Q
		public void switchQ(int p_index1, int p_index2)
		{
			Pointer<Integer, Integer> l_p1 = c_pointersQ.get(p_index1);
			Pointer<Integer, Integer> l_p2 = c_pointersQ.get(p_index2);
			int temp = l_p1.column;
			l_p1.column = l_p2.column;
			l_p2.column = temp;
		}
		
		public void shuffle()
		{
		    for (int i = c_pointersS.size(); i > 1; i--) {
		        int j = c_rand.nextInt(i);
		        
		        Pointer<Integer, Integer> temp = c_pointersS.get(j);
		        c_pointersS.set(j, c_pointersS.get(i-1));
		        c_pointersS.set(i-1, temp);
		        
		        temp = c_pointersQ.get(j);
		        c_pointersQ.set(j, c_pointersQ.get(i-1));
		        c_pointersQ.set(i-1, temp);
		    }
		}
		
		private void shuffleRange(int x, int y)
		{
		    // i is the number of items remaining to be shuffled.
		    for (int i = y; i > x + 1; i--) {
		        // Pick a random element to swap with the i-th element.
		        int j = c_rand.nextInt(i - x) + x;  // 0 <= j <= i-1 (0-based array)
		        // Swap array elements.
		        Pointer<Integer, Integer> temp = c_pointersS.get(j);
		        c_pointersS.set(j, c_pointersS.get(i-1));
		        c_pointersS.set(i-1, temp);
		    }
		}
		
		public void print()
		{
			for( int x = 0; x < c_pointersQ.size(); x++ )
			{
				Pointer<Integer, Integer> l_p = c_pointersQ.get(x);
				System.out.println("Q: " + l_p.row + " " + l_p.column);
				l_p = c_pointersS.get(x);
				System.out.println("S: " + l_p.row + " " + l_p.column);
			}
		}

		//Will test table sanity if each row of confirmation codes is 0 1 2 3 etc.
		public void test(String[][] p_tableQ, short[][] p_perms) {
			System.out.print("Testing table sanity...");
			for( int x = 0; x < c_pointersS.size(); x++ )
			{
				Pointer<Integer, Integer> l_p = c_pointersQ.get(x);
				int rowIndex = l_p.row;
				int columnIndex = l_p.column;
				l_p = c_pointersS.get(x);
				int finalColumn = l_p.column;
				
				if(Integer.parseInt(p_tableQ[rowIndex][columnIndex]) != finalColumn)
				{
					System.out.println("FAILED: " + rowIndex + " " + columnIndex + " : " + finalColumn);
				}
				if(p_perms[rowIndex][columnIndex] != Integer.parseInt(p_tableQ[rowIndex][columnIndex]))
				{
					System.out.println("FAILED: " + Integer.parseInt(p_tableQ[rowIndex][columnIndex]) + " " + columnIndex);
				}
			}
			System.out.println("DONE");
		}
		
		public void commit(File p_directory, CommitmentScheme p_cs) throws Exception
		{
			FlatFileTable l_table = new FlatFileTable();
			for( int x = 0; x < c_pointersS.size(); x++ )
			{
				ArrayList<Object> l_row = new ArrayList<Object>();
				Pointer<Integer, Integer> l_p = c_pointersQ.get(x);
				l_row.add(p_cs.commit(ByteBuffer.allocate(4).putInt(l_p.row).array()).c_commitment);
				l_row.add(p_cs.commit(ByteBuffer.allocate(4).putInt(l_p.column).array()).c_commitment);
				l_p = c_pointersQ.get(x);
				l_row.add(p_cs.commit(ByteBuffer.allocate(4).putInt(l_p.row).array()).c_commitment);
				l_row.add(p_cs.commit(ByteBuffer.allocate(4).putInt(l_p.column).array()).c_commitment);
				l_table.insertRow(l_row);
			}
			l_table.saveXmlFile(p_directory, "TableR");
		}
		
		public boolean[][] tally(boolean[][] p_votes, short[][] p_perms)
		{
			boolean[][] l_tableS = new boolean[c_ballots][c_columns];
			
			for( int x = 0; x < c_pointersQ.size(); x++ )
			{
				Pointer<Integer, Integer> l_p = c_pointersQ.get(x);
				short columnIndex = p_perms[l_p.row][l_p.column];
				if( p_votes[l_p.row][columnIndex] )
				{
					c_flags[x] = true;
					Pointer<Integer, Integer> l_sp = c_pointersS.get(x);
					l_tableS[l_sp.row][l_sp.column] = true; 
				}
			}
			
			return l_tableS;
		}

		//Fully reveals the pointers for the ballot IDs contained in p_ballotNums.  Saves
		//pointers to p_directory in a file named p_name
		public void fullAudit(int[] p_ballotNums, File p_directory, String p_name) {
			FlatFileTable l_table = new FlatFileTable();
			
			HashSet<Integer> l_ballotSet = new HashSet<Integer>();
			
			for( int x = 0; x < p_ballotNums.length; x++ )
				l_ballotSet.add(p_ballotNums[x]);
			
			for( int x = 0; x < c_pointersQ.size(); x++ )
			{
				ArrayList<Object> l_row = new ArrayList<Object>();
				
				Pointer<Integer, Integer> l_p = c_pointersQ.get(x);
				
				if( l_ballotSet.contains(l_p.row) )
				{
					l_row.add(l_p.row);
					l_row.add(l_p.column);
					l_p = c_pointersS.get(x);
					l_row.add(l_p.row);
					l_row.add(l_p.column);
					
					l_table.insertRow(l_row);
				}
			}
			
			l_table.saveXmlFile(p_directory, p_name);
		}

		public void randomAudit(Random c_rand, File p_directory, String p_name)
		{
			FlatFileTable l_table = new FlatFileTable();
			for( int x = 0; x < c_pointersQ.size(); x++ )
			{
				//Which side of the table will be revealed
				boolean l_side = c_rand.nextBoolean();
				
				ArrayList<Object> l_row = new ArrayList<Object>();
				
				if( l_side ) //Q pointer
				{
					Pointer<Integer, Integer> l_p = c_pointersQ.get(x);
					l_row.add(l_p.row);
					l_row.add(l_p.column);
					l_row.add("");
					l_row.add("");
				}
				else //S pointer
				{
					Pointer<Integer, Integer> l_p = c_pointersS.get(x);
					l_row.add("");
					l_row.add("");
					l_row.add(l_p.row);
					l_row.add(l_p.column);
				}
				l_table.insertRow(l_row);
			}
			
			l_table.saveXmlFile(p_directory, p_name);
		}
		
	}

