/*
 * @(#)SymmetricCommitmentScheme.java
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

import java.security.NoSuchAlgorithmException;
import java.security.SecureRandom;
import java.util.Arrays;

import javax.crypto.Cipher;
import javax.crypto.KeyGenerator;
import javax.crypto.NoSuchPaddingException;
import javax.crypto.SecretKey;
import javax.crypto.spec.SecretKeySpec;

public class SymmetricCommitmentScheme implements CommitmentScheme {

	Cipher c_cipher;
	SecureRandom c_rand;
	
	public SymmetricCommitmentScheme()
	{
		c_rand = new SecureRandom();
		try {
			c_cipher = Cipher.getInstance("AES");
		} catch (NoSuchAlgorithmException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (NoSuchPaddingException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
	
	public void setup( String p_cryptAlg, String p_randAlg )
	{
		try {
			c_rand = SecureRandom.getInstance(p_randAlg);
			c_cipher = Cipher.getInstance(p_cryptAlg);
		} catch (NoSuchAlgorithmException e) {
			System.err.println("Could not load alg: " + p_cryptAlg + " or " + p_randAlg);
			System.exit(-1);
		} catch (NoSuchPaddingException e) {
			System.err.println("Could not load cipher padding: " + p_cryptAlg);
			System.exit(-1);
		}
	}
	
	public byte[] commit(byte[] p_key, byte[] p_msg) throws Exception{
		//Generate random key
		KeyGenerator l_kgen = KeyGenerator.getInstance(c_cipher.getAlgorithm());
	    l_kgen.init(128);
	    
	    SecretKey l_skey = l_kgen.generateKey();
		
		//Encrypt data
		c_cipher.init(Cipher.ENCRYPT_MODE, p_key);
		byte[] l_commitData = c_cipher.doFinal(p_msg);
		//Return commitment
		return l_commitData;
	}

	public boolean decommit(byte[] data, Commitment commit) {
		try {
			c_cipher.init(Cipher.DECRYPT_MODE, new SecretKeySpec(commit.c_randSeed, c_cipher.getAlgorithm()));
			byte[] l_confirmation = c_cipher.doFinal(commit.c_commitment);
			return Arrays.equals(l_confirmation, data);
		} catch (Exception e)
		{
			return false;
		}
	}

}
