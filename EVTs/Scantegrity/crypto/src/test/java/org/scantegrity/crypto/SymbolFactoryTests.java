package org.scantegrity.crypto;
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

import java.security.SecureRandom;
import java.util.Arrays;

import org.junit.Test;
import org.scantegrity.crypto.SymbolFactory;


public class SymbolFactoryTests {

	/**
	 * @param args
	 * @throws Exception 
	 */
	@Test
	public void testSymbolFactoryGeneration() throws Exception
	{
		SymbolFactory l_sf = SymbolFactory.INSTANCE;
	    SecureRandom l_prng = SecureRandom.getInstance("SHA1PRNG");
	    String l_seed = "Hello there, Stranger!";
	    l_prng.setSeed(l_seed.getBytes());
	    
	    l_sf.initialize();
	    String[] l_tmp = { "" };
	    long l_start = System.currentTimeMillis();
	    for (int i = 0; i < 100; i++)
	    {
	    	l_tmp = l_sf.getCodes(l_prng, 10);
	    	System.out.println(Arrays.toString(l_tmp));
	    }
	    long l_end = System.currentTimeMillis();
	    //System.out.println(Arrays.toString(l_tmp));
	    
	    System.out.println("Completed in " + (l_end - l_start) + "ms.");
	    
	}
	
}
