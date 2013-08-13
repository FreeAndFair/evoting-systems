/**
  * This file is part of VoteBox.
  * 
  * VoteBox is free software: you can redistribute it and/or modify
  * it under the terms of the GNU General Public License version 3 as published by
  * the Free Software Foundation.
  * 
  * You should have received a copy of the GNU General Public License
  * along with VoteBox, found in the root of any distribution or
  * repository containing all or part of VoteBox.
  * 
  * THIS SOFTWARE IS PROVIDED BY WILLIAM MARSH RICE UNIVERSITY, HOUSTON,
  * TX AND IS PROVIDED 'AS IS' AND WITHOUT ANY EXPRESS, IMPLIED OR
  * STATUTORY WARRANTIES, INCLUDING, BUT NOT LIMITED TO, WARRANTIES OF
  * ACCURACY, COMPLETENESS, AND NONINFRINGEMENT.  THE SOFTWARE USER SHALL
  * INDEMNIFY, DEFEND AND HOLD HARMLESS RICE UNIVERSITY AND ITS FACULTY,
  * STAFF AND STUDENTS FROM ANY AND ALL CLAIMS, ACTIONS, DAMAGES, LOSSES,
  * LIABILITIES, COSTS AND EXPENSES, INCLUDING ATTORNEYS' FEES AND COURT
  * COSTS, DIRECTLY OR INDIRECTLY ARISING OUR OF OR IN CONNECTION WITH
  * ACCESS OR USE OF THE SOFTWARE.
 */

package votebox.crypto;

import java.io.File;
import java.io.FileOutputStream;
import java.io.OutputStream;

import sexpression.ASExpression;

import auditorium.Key;

/**
 * Used to generate ElGamal public/private key pairs.<BR>
 * Usage:
 *   java votebox.crypto.KeyGenerator [generator string] [number of keys] [output directory]
 * @author Montrose
 *
 */
public class KeyGenerator {

	/**
	 * @param args
	 */
	public static void main(String[] args) {
		if(args.length != 3){
			System.out.println("Usage:");
			System.out.println("\tjava votebox.crypto.KeyGenerator [generator string] [number of keys] [output directory]");
			System.exit(0);
		}//if
		
		int limit = -1;
		
		try{
			limit = Integer.parseInt(args[1]);
		}catch(Exception e){
			System.out.println("Expected integer for [number of keys], found \""+args[1]+"\".");
			System.out.println("\tError: "+e.getMessage());
			System.exit(0);
		}//catch
		
		File dir = null;
		
		try{
			dir = new File(args[2]);
			if(!dir.exists())
				dir.mkdirs();
		}catch(Exception e){
			System.out.println("Expected path for [output directory], found \""+args[2]+"\".");
			System.out.println("\tError: "+e.getMessage());
			System.exit(0);
		}//catch
		
		for(int i = 0; i < limit; i++){
			Pair<Key> keys = ElGamalCrypto.SINGLETON.generate(args[0]);
			Key publicKey = keys.get1();
			Key privateKey = keys.get2();
			
			ASExpression pub = publicKey.toASE();
			ASExpression priv = privateKey.toASE();
			
			File pubFile = new File(dir, i+"-public.key");
			File privFile = new File(dir, i+"-private.key");
			
			try{
				OutputStream out = new FileOutputStream(pubFile);
				out.write(pub.toVerbatim());
				out.flush();
				out.close();

				out = new FileOutputStream(privFile);
				out.write(priv.toVerbatim());
				out.flush();
				out.close();
			}catch(Exception e){
				System.out.println("Encountered error writing key files.");
				System.out.println("\tError: "+e.getMessage());
				System.exit(0);
			}//catch
		}//for
	}

}
