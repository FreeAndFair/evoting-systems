/*
 * @(#)PunchscanEngine.java
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
 * @author John L. Conway IV 
 */

package org.scantegrity.crypto.punchscan;

import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.security.SecureRandom;
import java.util.InvalidPropertiesFormatException;
import java.util.Properties;
import java.util.Random;

import org.scantegrity.crypto.Commitment;
import org.scantegrity.crypto.CommitmentScheme;
import org.scantegrity.crypto.PRNGCommitmentScheme;


public class PunchscanEngine {
	static final String DEFAULT_NUM_BALLOTS = "100"; 
	static final String DEFAULT_MAX_CANDIDATES = "100";
	static final String DEFAULT_RAND_PROVIDER = "SUN";
	static final String DEFAULT_RAND_ALG = "SHA1PRNG";
	static final boolean DEBUG = true; 
	
	private SimplePermutation c_sperm; 
	private int c_numBallots; 
	private int c_maxCandidates; 
	private CommitmentScheme c_cs;
	private String c_propertiesFile;
	private SecureRandom c_sr;
	private DTable c_dTable; 
	private RTable c_rTable; 
	
	/**
	 * The constructor for the Punchscan Engine. This will look at the 
	 * .properties file and determine the number of candidates,
	 *  and handle all other setup information. 
	 */
	public PunchscanEngine(CommitmentScheme p_cs, String p_propertiesFile) {
		c_propertiesFile = p_propertiesFile; 
		
		//load the properties from the properties file
		FileInputStream l_propxml = null;
		try {
			l_propxml = new FileInputStream(c_propertiesFile);
		} catch (FileNotFoundException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
		Properties l_prop = new Properties();
		
		try {
			l_prop.loadFromXML(l_propxml);
		} catch (InvalidPropertiesFormatException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
		c_numBallots = Integer.parseInt(l_prop.getProperty("NumBallots", DEFAULT_NUM_BALLOTS));
		c_maxCandidates = Integer.parseInt(l_prop.getProperty("MaxCandidates", DEFAULT_MAX_CANDIDATES));
		
		//set up random number generator
		try
		{
			String l_randAlgName = l_prop.getProperty("SecureRandomAlgorithm", DEFAULT_RAND_ALG);
			String l_randProviderName = l_prop.getProperty("SecureRandomProvider", DEFAULT_RAND_PROVIDER);
			c_sr = SecureRandom.getInstance(l_randAlgName, l_randProviderName);
			
		} catch (Exception e) {
			//If there is some exception loading the properties file or initializing the primitives, revert to system defaults
			c_sr = new SecureRandom();
		}
		
		//set up the permutation engine
		c_sperm = new SimplePermutation(c_maxCandidates);
		
		c_cs = p_cs; 
	}
	
	/**
	 * Generate
	 * 
	 * This generates all the backend tables and commits to everything, returning the 
	 * commitments to the frontend that calls this. This is for the initial 
	 * generation and commitment of the backend. 
	 */
	public Commitment[][] generate(int p_candidatePermutation[][][])
	{
		Commitment l_commits[][] = new Commitment[2][]; 
		generateTables(p_candidatePermutation); 
		c_dTable.shuffle(); 
		l_commits[0] = c_dTable.commitToRows(c_cs);
		l_commits[1] = c_dTable.commitCols(c_cs);
		return l_commits; 
	}
	
	/** 
	 * The pre-election audit is a row audit where 
	 * we pick random rows and release their commitments. 
	 * 
	 * We will be given a list of ballot ID's and 
	 * reveal those commitments.  
	 */
	public Commitment[] preElectionAudit(int p_ballotIds[], int p_candidatePermutations[][][])
	{
		//rebuild the table
		generateTables(p_candidatePermutations);
		
		//get a pointer to all the commitments while the table is still in order
		Commitment[] l_commits = new Commitment[p_ballotIds.length];
		for(int i = 0; i < p_ballotIds.length; i++)
		{
			l_commits[i] = c_dTable.getRow(i).getCommit(); 
		}
		
		//shuffle the table
		c_dTable.shuffle(); 
		
		//commit the rows
		c_dTable.commitRows(c_cs); 
		
		//return those commitments
		return l_commits; 
	}
	
	public Commitment postElectionAudit(int p_column, int p_candidatePermutations[][][])
	{
		//rebuild the table
		generateTables(p_candidatePermutations);
		
		//TODO
		
		//commit the columns
		
		//get the commits for the column requested
		
		//return those commitments
		return null; 
	}
	
	public void results(int p_results[][], int p_candidatePermutations[][][])
	{
		//rebuild the table
		generateTables(p_candidatePermutations);
		
		for(int i = 0; i < p_results.length; i++)
		{
			c_dTable.getRow(i).sendResult(p_results[i]);
		}
	} 
	
	
	/* *******************************************************
	 * 
	 * Private Methods
	 * 
	 * *******************************************************/
	
	private void generateTables(int p_candidatePermutations[][][])
	{
		c_rTable = new RTable(c_numBallots, c_sr);
		c_dTable = generateDTable(p_candidatePermutations, c_rTable);
		
		//shuffle rTable
		c_rTable.shuffle(); 
	}
	
	/**
	 * This method generates the entire backend table.
	 * 
	 * @param candidatePermutations[][][] - These are the initial permutations 
	 * 	from the frontend. The lowest level array is the array of indexes for the 
	 * 	actual permutation put into an array of contests for each ballot, put into the 
	 *  last array of ballots. 
	 * @return DTable The dTable
	 */
	private DTable generateDTable(int p_candidatePermutations[][][], RTable p_rTable)
	{
		DTable l_table = new DTable(p_candidatePermutations.length, c_sr);
		//for each ballot, generate each row
		for(int i = 0; i < p_candidatePermutations.length; i++)
		{
			DRow l_row = generateRow(i, p_candidatePermutations[i]);
			l_table.add(l_row, i); 
			p_rTable.addResult(i, l_row.getResPtr());
		}
		
		return l_table;
	}
	
	/**
	 * This method will generate one row of the table given 
	 * an initial Ballot ID and Vector of Candidate Orders
	 * 
	 * @param candidatePermutations[][]: This is an array of permutations per contest
	 * @return DRow the row
	 */
	private DRow generateRow(int p_ballotID, int p_candidatePermutations[][])
	{	
		int l_inputPerm[][] = p_candidatePermutations;
		int l_permA[][] = new int[l_inputPerm.length][c_maxCandidates];
		
		//for each contest, grab a permutation
		for(int j = 0; j < l_inputPerm.length; j++)
		{
			l_permA[j] = c_sperm.getPerm();
		}
		
		//ok now create the inverse perm
		int l_permB[][] = new int[p_candidatePermutations.length][c_maxCandidates];
		
		//find the inverse
		for(int j = 0; j < l_inputPerm.length; j++)
		{
			int l_I[] = l_inputPerm[j]; 
			
			for(int k = 0; k < l_I.length; k++)
			{
				l_permB[j][l_permA[j][l_I[k]]] = l_I[k]; ;
			}
		} 
		
		return new DRow(p_ballotID, l_permA, l_permB);
	}
	
	
	/* *******************************************************
	 * 
	 * All Methods Below For Testing only
	 * 
	 *********************************************************/
	public void Test()
	{	
		int l_numContests = 1;
		
		//create the initial candidate list
		int l_initial[][] = new int[l_numContests][c_maxCandidates];
		for(int i = 0; i < l_numContests; i++)
		{
			for(int j = 0; j < c_maxCandidates; j++)
			{
				l_initial[i][j] = j;
			}
		}
		
		//test just the first row
		for(int i = 0; i < c_numBallots; i++)
		{
			generateRow(i, l_initial);
		}
		
		generateRow(4,l_initial);
		generateRow(2,l_initial);
		generateRow(6,l_initial); 
	}
	
	
	
	/*
	 * Test until I figure out how to do the junit tests or whatever
	 */
	public static void main(String args[])
	{	
		//create the engine
		PunchscanEngine l_engine = new PunchscanEngine(new PRNGCommitmentScheme(), "Config.properties");
		l_engine.Test(); 
	}
	
	
	/* *************************************
	 * Utility methods to print arrays
	 * @param p_array
	 ***************************************/
	@SuppressWarnings("unused")
	private void printArray(int p_array[])
	{
		System.out.println("Dumping array:");
		for(int i = 0; i < p_array.length; i++)
		{
			System.out.print(p_array[i]); 
		}
		System.out.println(); 
	}
	
	@SuppressWarnings("unused")
	private void printArray(int p_array[][])
	{
		System.out.println("Dumping array:");
		for(int i = 0; i < p_array.length; i++)
		{
			for(int j = 0; j < p_array[i].length; j++)
			{
				System.out.print(p_array[i][j]);	
			} 
			System.out.println(); 
		}
		System.out.println(); 
	}
}
