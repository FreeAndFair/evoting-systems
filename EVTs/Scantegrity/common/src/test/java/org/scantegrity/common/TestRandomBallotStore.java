/*
 * @(#)TestRandomBallotStore.java
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

import java.io.File;
import java.io.IOException;
import java.security.NoSuchAlgorithmException;
import java.util.Vector;

import org.junit.Test;
import org.scantegrity.common.Ballot;
import org.scantegrity.common.RandomBallotStore;

/**
 * @author Richard Carback
 *
 */
public class TestRandomBallotStore
{

	/**
	 * @param args
	 * @throws IOException 
	 * @throws NoSuchAlgorithmException 
	 */
	@Test
	public void testBallotStore() throws IOException, NoSuchAlgorithmException
	{
		File l_x = new File("./ballots.sbr");
		l_x.delete();
		RandomBallotStore l_store = new RandomBallotStore(314159, 10*1024*1024, 512, "./ballots.sbr", null, null);
		l_store.initializeStore();
		RandomBallotCreator l_c = new RandomBallotCreator();
		Vector<Ballot> l_ballots = new Vector<Ballot>();
		Vector<Ballot> l_read = new Vector<Ballot>();
		
		
		for (int l_i = 0; l_i < 10; l_i++)
		{
			l_ballots.add(l_c.getBallot());
			l_store.addBallot(l_ballots.lastElement());
		}
		
		l_store.close();
		
		l_store.open();
		l_read = l_store.getBallots();
		
		for (int l_i = 0; l_i < l_ballots.size(); l_i++)
		{
			if (!l_ballots.contains(l_read.get(l_i))) {
				System.out.println("Ballot Missing: " + l_read.get(l_i).getId());
			}
			else
			{
				System.out.println("Ballot Found: " + l_read.get(l_i).getId());	
			}
		}		
		
		l_store.close();
		
		
	}

}
