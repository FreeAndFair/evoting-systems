/*
 * @(#)SymbolFactory.java
 *  
 * Copyright (C) Scantegrity Project
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

import java.security.SecureRandom;
import java.util.HashMap;
import java.util.Vector;

/**
 * SymbolFactory generates confirmation numbers for Scantegrity ballots.  
 * SymbolFactory should only have 1 instance, and is implemented as a singleton. 
 * 
 * Users of this class should never reseed or reuse the RNG they send to this 
 * class while they are using it, as it is important to reproduce symbols in the 
 * exact order during subsequent operations in the voting protocol. 
 * 
 * 	TODO: Set a limit on the size of the pre-generated code list, and fall back to a 
 * slower generation algorithm if necessary. Current length min is 1 and max is 10,
 * so unless the symbol list gets really big this should not be a problem.
 * 
 * TODO: Add minimum entropy requirement on this class. If any combination of
 * settings causes us to dip below, say 10, possible elements, then throw an 
 * exception.
 * 
 * 
 * @author Richard Carback
 * @version 0.0.1
 * @date 2/27/11
 */

public enum SymbolFactory {
	INSTANCE;
	
	// TODO: Move these to a constants folder, assuming more than one class can use them?
	private final static String EXUNIQUE = "SymbolGenerator: Cannot produce {0} unique codes with current settings!";
	private final static String EXNOWORDS = "SymbolGenerator: cannot produce any code words.";
	private final static String EXZEROSTR = "SymbolGenerator: Cannot use a zero-length string.";
	
	private String c_symbols = "0123456789";
	private Integer c_codeLen = 3;
	private String[] c_forbidden = { "" };
	private String[] c_codeList = null;

	/**
	 * This function initializes the symbol factory to use the defaults. By default, 
	 * this class should work, so it does almost nothing, but it will pre-generate
	 * the code list which could speed up return time from the first call.
	 * 
	 * This function has the effect of checking the validity of your current setup.
	 * 
	 * @param p_codeLen
	 * @param p_symbols
	 * @return
	 */
	public boolean initialize()
	{
		return initialize(c_codeLen, c_symbols, c_forbidden);
	}

	/**
	 * This function initializes the symbol factory to use the defaults and return
	 * p_codeLen sized words. 
	 * 
	 * @param p_codeLen
	 * @param p_symbols
	 * @return
	 */
	public boolean initialize(Integer p_codeLen)
	{
		return initialize(p_codeLen, c_symbols, c_forbidden);
	}

	/**
	 * This function initializes the symbol factory with the given parameters. It
	 * uses the default for forbidden strings.
	 * 
	 * @param p_codeLen
	 * @param p_symbols
	 * @return
	 */
	public boolean initialize(Integer p_codeLen, String p_symbols)
	{
		return initialize(p_codeLen, p_symbols, c_forbidden);
	}

	/**
	 * This function initializes the symbol factory with the given parameters. 
	 * 
	 * @param p_codeLen
	 * @param p_symbols
	 * @param p_forbidden
	 * @return
	 */
	public boolean initialize(Integer p_codeLen, String p_symbols, String[] p_forbidden)
	{
		try 
		{
			setCodeLen(p_codeLen);
			setSymbols(p_symbols);
			setForbidden(p_forbidden);
			genCodeList();
		} catch (Exception e)
		{
			System.err.println(e.getMessage());
			return false;
		}
		return true;
	}
	
	/**
	 * Use the given SPRNG to generate p_numCodes unique code words. 
	 * 
	 * You must use the SPRNG consistently with the same seed if you want to 
	 * reproduce the same code words. This class assumes you have properly 
	 * seeded the generator.
	 * 
	 * @param p_sprng a pre-seeded secure pseudo-random number generator.
	 * @param p_num the number of unique codes to produce.
	 * @throws Exception 
	 */ 
	public String[] getCodes(SecureRandom p_sprng, int p_num) throws Exception
	{
		if (c_codeList == null) genCodeList();		

		// Note: this gets called a lot, it needs to be fast, and it can't introduce bias!
		//Current implementation is probably not as fast as it could be...
		
		//TODO: Not sure if 2*p_num is the best idea.
		HashMap<Integer, Integer> l_shuf = new HashMap<Integer, Integer>(2*p_num);
		String[] l_codes = new String[p_num];
		int i;
		int l_t = 0;
		int l_last = c_codeList.length;

		if (p_num > l_last)
		{
			throw new Exception(String.format(EXUNIQUE, p_num));
		}
		
		for (i = p_num; --i >= 0; ) // this is awful, but faster than the status quo
		{
			//"nextInt" claims to be uniformly distributed...
			l_t = p_sprng.nextInt(l_last);
			
			//If it exists in the hashmap, take the index in the hasmap, this is
			// an old "max" value.
			if (l_shuf.get(l_t) != null)
			{
				l_codes[i] = c_codeList[l_shuf.get(l_t)];
			}
			else
			{
				l_codes[i] = c_codeList[l_t];
			}

			//Set this position to the current max, if the alg already selected max this
			//doesn't do anything since max won't come up again.
			if (l_shuf.get(--l_last) == null) 
			{
				l_shuf.put(l_t, l_last);
			}
			else
			{
				l_shuf.put(l_t, l_shuf.get(l_last));
			}
		}
		
		return l_codes;
	}

	/**
	 * Generate each possible code word, and remove all the forbidden code 
	 * words. This can potentially cause memory issues, but since we usually
	 * limit code lengths, the numbers are generally small. 
	 * @throws Exception 
	 */
	private void genCodeList() throws Exception
	{
		Vector<String> l_tmp = new Vector<String>();
		
		char[] l_cur = new char[c_codeLen];
		char[] l_last = new char[c_codeLen];
		int[] l_ctrs = new int[c_codeLen];
		
		for (int i = 0; i  < c_codeLen; i++)
		{
			l_cur[i] = c_symbols.charAt(0);
			l_last[i] = c_symbols.charAt(c_symbols.length()-1);
			l_ctrs[i] = 0;
		}
		
		//This particular loop produces each permutation in inverse of the
		//way you might do it on paper (easier to start at 0 vice len-1).
		while (!java.util.Arrays.equals(l_cur, l_last))
		{
			l_tmp.add(new String(l_cur));
			
			boolean l_cascade = true;
			int i = 0; 
			while (l_cascade == true && i < c_codeLen)
			{
				l_ctrs[i]++;
				if (l_ctrs[i] < c_symbols.length())
				{
					l_cascade = false; //This breaks the loop.
				}
				else
				{
					l_ctrs[i] = 0;
				}
				l_cur[i] = c_symbols.charAt(l_ctrs[i]);
				i++;
			}
		}
		l_tmp.add(new String(l_cur));
		
		//Remove forbidden
		for (int i = 0; i < c_forbidden.length; i++)
		{
			l_tmp.remove(c_forbidden[i]);			
		}
		
		if (l_tmp.size() <= 0) throw new Exception(EXNOWORDS);
		
		c_codeList = l_tmp.toArray(new String[l_tmp.size()]);
	}
	
	
	/**
	 * Set the symbols produced by this class. Length of the string must be > 0 
	 * and duplicate characters will be removed from the string.
	 * 
	 * @param p_symbols the symbols used to generate the codes.
	 * @throws Exception 
	 */	
	public void setSymbols(String p_symbols) throws Exception {
		if (p_symbols.length() > 0)
		{
			//Remove duplicates in the String
			char[] l_sorted = p_symbols.toCharArray();
			java.util.Arrays.sort(l_sorted);
			c_symbols = "" + l_sorted[0];
			for (int i = 1; i < l_sorted.length; i++)
			{
				while(l_sorted[i-1] == l_sorted[i]) i++;
				if (i < l_sorted.length)
				{
					c_symbols += l_sorted[i];
				}
			}
		}
		else
		{
			throw new Exception(EXZEROSTR);
		}
	}
	
	/**
	 * Get the current symbol list.
	 * 
	 * @return the symbols used to generate codes.
	 */
	public String getSymbols() {
		return c_symbols;
	}
	
	/**
	 * Forbidden strings that should never be produced by the generator. 
	 * 
	 * @param p_forbidden an array of forbidden codes
	 */
	public void setForbidden(String[] p_forbidden) {
		c_forbidden = p_forbidden;
	}
	
	/**
	 * Get the current list of forbidden code words.
	 * 
	 * @return the forbidden code words.
	 */
	public String[] getForbidden() {
		return c_forbidden;
	}
	
	/**
	 * Set the length of each code word. Min 1 and Max 10. 
	 * 
	 * @param codeLen the codeLen to set
	 */
	public void setCodeLen(Integer p_codeLen) {
		if (p_codeLen > 10) p_codeLen = 10;
		if (p_codeLen < 1) p_codeLen = 1;
		c_codeLen = p_codeLen;
	}

	/**
	 * Get the length of each code word.
	 * 
	 * @return the codeLen
	 */
	public Integer getCodeLen() {
		return c_codeLen;
	}
}
