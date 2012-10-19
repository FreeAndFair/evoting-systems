/*
 * @(#)HashCommitmentScheme.java
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

import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.security.SecureRandom;
import java.util.Arrays;

public class HashCommitmentScheme implements CommitmentScheme {

	MessageDigest c_digest;
	int c_saltLength;
	SecureRandom c_rand;
	
	public HashCommitmentScheme()
	{
		try {
			c_digest = MessageDigest.getInstance("SHA-512");
		} catch (NoSuchAlgorithmException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		c_saltLength = 256;
		c_rand = new SecureRandom();
	}
	
	public void setup(String p_hashAlg, int p_saltLength, String p_randAlg)
	{
		try {
			c_digest = MessageDigest.getInstance(p_hashAlg);
			c_rand = SecureRandom.getInstance(p_randAlg);
		} catch (NoSuchAlgorithmException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		c_saltLength = p_saltLength;
	}
	
	public Commitment commit(byte[] data) throws Exception {
		c_digest.reset();
		c_digest.update(data);
		byte[] l_salt = new byte[c_saltLength];
		c_rand.nextBytes(l_salt);
		c_digest.update(l_salt);
		byte[] l_hash = c_digest.digest();
		
		Commitment l_commit = new Commitment(l_hash, l_salt);
		return l_commit;
	}

	public boolean decommit(byte[] data, Commitment commit) {
		c_digest.reset();
		c_digest.update(data);
		c_digest.update(commit.c_randSeed);
		byte[] l_confirmation = c_digest.digest();
		
		return Arrays.equals(l_confirmation, commit.c_commitment);
	}

}
