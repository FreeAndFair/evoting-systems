/*
 * @(#)PRNGCommitmentScheme.java
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

package org.scantegrity.crypto;

import java.math.BigInteger;
import java.security.SecureRandom;
import java.util.Arrays;


public class PRNGCommitmentScheme implements CommitmentScheme {

	byte[] c_challenge;
	SecureRandom c_rand;
	
	public PRNGCommitmentScheme()
	{
		c_rand = new SecureRandom();
	}
	
	public void initialize(byte[] p_challenge)
	{
		//TODO: Really only one challenge is necessary, or is it one per commit?
		//Need to check if this is lending itself to a secure implementation. If
		//not, then should use a Map of keys to challenges.
		c_challenge = p_challenge.clone();
	}
	
	//http://www.springerlink.com/index/N615G60560417356.pdf
	
	public byte[] commit(byte[] p_key, byte[] p_msg) throws Exception {
		if( c_challenge == null )
		{
			c_challenge = new byte[4096];
			c_rand.nextBytes(c_challenge);
		}
		
		if( p_msg.length > c_challenge.length )
			throw new Exception("Message is longer than challenge input");
				
		//Generate the random bits to XOR with the data
		SecureRandom l_rand = SecureRandom.getInstance("SHA1PRNG");
		l_rand.setSeed(p_key);
		byte[] l_randBytes = new byte[c_challenge.length * 4];
		l_rand.nextBytes(l_randBytes);
		
		//Multiply the data by the challenge
		BigInteger l_challengeBig = new BigInteger(1, c_challenge);
		BigInteger l_dataBig = new BigInteger(1, p_msg);
		byte[] l_res = l_challengeBig.multiply(l_dataBig).toByteArray();
		
		for(int x = 0; x < l_randBytes.length; x++ )
		{
			if( x < l_res.length )
				l_randBytes[x] = (byte) (l_randBytes[x] ^ l_res[x]);
		}
		
		return l_randBytes;
		
	}

	/* (non-Javadoc)
	 * @see org.scantegrity.crypto.CommitmentScheme#verify(byte[], byte[], byte[])
	 */
	@Override
	public boolean verify(byte[] p_commit, byte[] p_key, byte[] p_msg) {
		try {
			byte[] l_tst = commit(p_key, p_msg);
			if (Arrays.equals(l_tst, p_commit)) return true;
		} catch (Exception e) {
			e.printStackTrace();
		}
		
		return false;
	}
}
