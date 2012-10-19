/*
 * @(#)App.java
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
package e2e;
import java.io.File;
import java.io.FileInputStream;
import java.security.SecureRandom;
import java.util.Properties;

import org.scantegrity.crypto.Commitment;
import org.scantegrity.crypto.SymmetricCommitmentScheme;
import org.scantegrity.crypto.scantegrity.ScantegrityFrontEnd;



/**
 * Hello world!
 *
 */
public class App 
{
	static final String DEFAULT_RAND_PROVIDER = "SUN";
	static final String DEFAULT_RAND_ALG = "SHA1PRNG";
	
    public static void main( String[] args )
    {
    	SecureRandom l_rand;
    	
    	try {
			FileInputStream l_propxml = new FileInputStream("Config.properties");
			Properties l_prop = new Properties();
			l_prop.loadFromXML(l_propxml);
			
			String l_randAlgName = l_prop.getProperty("SecureRandomAlgorithm", DEFAULT_RAND_ALG);
			String l_randProviderName = l_prop.getProperty("SecureRandomProvider", DEFAULT_RAND_PROVIDER);
			l_rand = SecureRandom.getInstance(l_randAlgName, l_randProviderName);
			
		} catch (Exception e) {
			//If there is some exception loading the properties file or initializing the primitives, revert to system defaults
			l_rand = new SecureRandom();
		}
		
		SymmetricCommitmentScheme l_commitScheme = new SymmetricCommitmentScheme();
		l_commitScheme.setup("AES","SHA1PRNG");
		//HashCommitmentScheme l_commitScheme = new HashCommitmentScheme();
		//l_commitScheme.setup("SHA-512", 256, "SHA1PRNG");
		//PRNGCommitmentScheme l_commitScheme = new PRNGCommitmentScheme();
		System.out.println("Generating test data...");
		
		byte[][] l_test = new byte[2][4096];
		for( int x = 0; x < l_test.length; x++ )
		{
			l_rand.nextBytes(l_test[x]);
		}
		
		long l_start = System.currentTimeMillis();
		System.out.print("Testing commit sanity...");
		for( int x = 0; x < l_test.length; x++ )
		{
			try {
				Commitment l_testCommit = l_commitScheme.commit(l_test[x]);
				if( !l_commitScheme.decommit(l_test[x], l_testCommit) )
					System.out.println("FAILED");
			} catch (Exception e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}
		System.out.println("DONE");
		
		System.out.println(System.currentTimeMillis() - l_start);
		
		//Test data
		String[][] l_codes = new String[3][3];
		l_codes[0] = new String[]{"0", "1", "2"};
		l_codes[1] = new String[]{"0", "1", "2"};
		l_codes[2] = new String[]{"0", "1", "2"};
		boolean[][] l_votes = new boolean[3][3];
		l_votes[0] = new boolean[]{true, false, false};
		l_votes[1] = new boolean[]{false, true, false};
		l_votes[2] = new boolean[]{false, false, true};
		
		/*ScantegrityEngine l_scantegrity = new ScantegrityEngine(l_rand, new File("/Users/Travis/Desktop/"), l_commitScheme);
		try {
			l_scantegrity.preElection(l_codes);
			System.out.print("Print audit...");
			l_scantegrity.fullAudit(new int[]{0,1}, "PrintAudit");
			System.out.println("DONE");
			System.out.print("Post election...");
			l_scantegrity.postElection(l_votes);
			System.out.println("DONE");
			System.out.print("Partial audit...");
			l_scantegrity.randomAudit("PartialAudit");
			System.out.println("DONE");
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}*/
		System.out.print("Generating ballots...");
		ScantegrityFrontEnd l_frontEnd = new ScantegrityFrontEnd(l_rand, 5000, 4, new File("/Users/Travis/Desktop"), l_commitScheme);
		try
		{
			l_frontEnd.preElection();
		}
		catch(Exception e)
		{
			e.printStackTrace();
		}
		System.out.println("DONE");
    }
}
