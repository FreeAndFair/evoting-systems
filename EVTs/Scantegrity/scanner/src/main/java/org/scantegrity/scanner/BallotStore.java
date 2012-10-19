/*
 * @(#)BallotStore.java.java
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
package org.scantegrity.scanner;

import java.beans.XMLDecoder;
import java.beans.XMLEncoder;
import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.security.NoSuchAlgorithmException;
import java.security.SecureRandom;
import java.util.Enumeration;
import java.util.Vector;
import java.util.jar.JarEntry;
import java.util.jar.JarFile;
import java.util.jar.JarOutputStream;
import java.util.jar.Manifest;

import org.scantegrity.common.Ballot;


/**
 * Used to store scanned ballots. Eventually this should hide the order
 * of the files as they were added. 
 * 
 * @author Richard Carback
 *
 */
public class BallotStore
{
	private Vector<Integer> c_ballotIds;
	private Vector<JarFile> c_store;
	private SecureRandom c_csprng;
	
	/**
	 * Default constructor, creates one store called Ballots.jar in the default
	 * classpath. 
	 * @throws IOException
	 * @throws NoSuchAlgorithmException 
	 */
	public BallotStore() throws IOException, NoSuchAlgorithmException
	{
		c_ballotIds = new Vector<Integer>();
		c_store = new Vector<JarFile>();
		c_store.add(new JarFile("Ballots.jar"));
		c_csprng = SecureRandom.getInstance("SHA1PRNG");
		c_csprng.setSeed(System.currentTimeMillis());
	}
	
	/**
	 * Takes a vector of filenames and creates a ballot store for each one.
	 * 
	 * @param p_locations
	 * @throws IOException
	 * @throws NoSuchAlgorithmException 
	 */
	public BallotStore(Vector<String> p_names) throws IOException, NoSuchAlgorithmException
	{
		this(p_names, null);
	}
	
	/**
	 * Takes a vector of filenames and creates a ballot store for each one.
	 * Also, takes a csprng. 
	 * @param p_ballot
	 * @throws IOException 
	 * @throws NoSuchAlgorithmException 
	 */
	public BallotStore(Vector<String> p_names, SecureRandom p_csprng) throws IOException, NoSuchAlgorithmException
	{
		c_ballotIds = new Vector<Integer>();
		c_store = new Vector<JarFile>();
		for (String l_s : p_names)
		{
			File l_f = new File(l_s);
			
			if(!l_f.exists())
			{
				l_f.createNewFile();
				JarOutputStream l_j = new JarOutputStream(new FileOutputStream(l_f), new Manifest());
				l_j.close(); 
			}
			
			c_store.add(new JarFile(l_f));			
		}			
		if (p_csprng == null)
		{
			c_csprng = SecureRandom.getInstance("SHA1PRNG");
			c_csprng.setSeed(System.currentTimeMillis());
		}
	}
	
	/**
	 * NOTE: This does not scale very well.
	 * 
	 * @param p_ballot
	 * @throws IOException
	 */
	public void add(Ballot p_ballot) throws IOException
	{
		String l_eName;
		//Find an unused filename
		do
		{
			 l_eName = "Ballot-" + c_csprng.nextInt() + ".xml";
		} while (c_store.get(0).getEntry(l_eName) != null); 
		
		JarEntry l_e = new JarEntry(l_eName);
		l_e.setTime(0);
		Enumeration<JarEntry> l_entries = c_store.get(0).entries();
		Vector<JarEntry> l_newEntries = new Vector<JarEntry>();
		Vector<ByteArrayOutputStream> l_out = new Vector<ByteArrayOutputStream>();
		while (l_entries.hasMoreElements())
		{
			JarEntry l_tmp = l_entries.nextElement();
			l_tmp.setTime(0);
			ByteArrayOutputStream l_s = new ByteArrayOutputStream();
			if (l_e != null && l_e.getName().compareTo(l_tmp.getName()) < 0)
			{
				XMLEncoder l_enc = new XMLEncoder(l_s);
				l_enc.writeObject(p_ballot);
				l_enc.close();
				l_newEntries.add(l_e);
				l_out.add(l_s);
				l_e = null;
				l_s = new ByteArrayOutputStream();
			}
			int l_bread;
			byte l_buf[] = new byte[1024];
			InputStream l_stream = c_store.get(0).getInputStream(l_tmp);
	        while ((l_bread = l_stream.read(l_buf)) != -1) {
                l_s.write(l_buf, 0, l_bread);
                if(l_bread == 0)
                	break;
           }
	       l_newEntries.add(l_tmp);
	       l_out.add(l_s);
		}
		
		for (int l_i = 0; l_i < c_store.size(); l_i++)
		{
			rewriteJar(l_i, l_newEntries, l_out);			
		}
		
		if (p_ballot.isCounted() == true) c_ballotIds.add(p_ballot.getId());
	}
	
	/**
	 * @param p_jar
	 * @param p_entries
	 * @param p_out
	 * @throws IOException 
	 * @throws FileNotFoundException 
	 */
	private void rewriteJar(int p_id, Vector<JarEntry> p_entries,
			Vector<ByteArrayOutputStream> p_out) throws FileNotFoundException, IOException
	{
		String l_name = c_store.get(0).getName();
		JarOutputStream l_outFile = new JarOutputStream(
				new FileOutputStream(l_name + ".tmp"));
		
		try
		{
			for (int l_i = 0; l_i < p_entries.size(); l_i++)
			{
				byte l_b[] = p_out.get(l_i).toByteArray();
				l_outFile.putNextEntry(p_entries.get(l_i));
				l_outFile.write(l_b, 0, l_b.length);
			}
		}
		finally
		{
			l_outFile.close();
		}
		
		c_store.get(p_id).close();
		File l_f = new File(l_name);
		l_f.delete();
		
		File l_new =  new File(l_name + ".tmp");
		l_new.renameTo(l_f);
		
		c_store.set(p_id, new JarFile(l_name));
	}

	/**
	 * Gets all the ballots in the first JarFile.
	 * @return
	 * @throws IOException 
	 */
	public Vector<Ballot> getBallots() throws IOException
	{
		Vector<Ballot> l_ballots = new Vector<Ballot>();
		Enumeration<JarEntry> l_entries = c_store.get(0).entries();
		JarEntry l_e;
		XMLDecoder l_dec;
		while (l_entries.hasMoreElements())
		{
			l_e = l_entries.nextElement();
			if(l_e.isDirectory() || l_e.getName().equals("META-INF/MANIFEST.MF"))
				continue;
			l_dec = new XMLDecoder(c_store.get(0).getInputStream(l_e));
			l_ballots.add((Ballot)l_dec.readObject());
			l_dec.close();
		}
		
		return l_ballots;
		
	}
	
	/**
	 * Tells you if you have already scanned a ballot.
	 * 
	 * @param p_ballotId
	 * @return
	 */
	public boolean isDuplicate(Integer p_ballotId)
	{
		return c_ballotIds.contains(p_ballotId);
	}
}
