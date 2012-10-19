/*
 * @(#)FindFile.java.java
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
import java.util.ArrayList;
import java.util.ListIterator;
import java.util.Vector;
import java.util.regex.Pattern;

import org.scantegrity.common.constants.FindFileConst;

/**
 * @author John Conway
 *
 * Using regex, will find a file on any OS
 */
public class FindFile extends Thread
{
	//String variables
	private String c_filename;
	private String c_osname;
	
	//threads running array
	private ArrayList<Thread> c_threadList;
	
	//directory stack
	private ArrayList<SearchDirectory> c_dirToSearch;
	
	//reference to parent
	private FindFile c_parent; 
	
	//Configuration File
	private Vector<File> c_filesFound;
	
	//flag for config found
	private boolean c_isConfigFound = false;
	
	//Depth of directories to recurse
	public int c_recurseDepth = -1;
	private boolean c_findMultiple = false;
	
	private Pattern c_pattern = null;
	private AsyncFindListener c_finder = null;
	
	public interface AsyncFindListener
	{
		public void report(File p_file);
	}
	
	class SearchDirectory
	{
		public int depth;
		public File directory;
		public SearchDirectory(int p_depth, File p_directory)
		{
			depth = p_depth;
			directory = p_directory;
		}
	}
	

	/**
	 * Searches for a file based on a regular expression for that file
	 * 
	 * @param p_regex : regular expression for the filename
	 */
	public FindFile()
	{
		c_filename = null;
		c_dirToSearch = new ArrayList<SearchDirectory>(); 
		c_parent = null; 
		c_filesFound = null;
		
		determineOS(); 
		
		getPathsToSearch(); 
	}
	
	public FindFile(Pattern p_pattern)
	{
		c_pattern = p_pattern;
		c_dirToSearch = new ArrayList<SearchDirectory>();
		c_parent = null;
		c_filesFound = new Vector<File>();
		
		determineOS(); 
		
		getPathsToSearch(); 
	}
	
	/**
	 * This constructor takes an exact file to search for 
	 * @param p_filename : the filename to search for
	 */
	public FindFile(String p_filename)
	{
		c_filename = p_filename; 
		c_dirToSearch = new ArrayList<SearchDirectory>();
		c_parent = null;
		c_filesFound = new Vector<File>();
		
		determineOS(); 
		
		getPathsToSearch(); 
	}
	
	/**
	 * Takes a path to search down from 
	 * 
	 * @param p_dirToSearch
	 */
	public FindFile(FindFile p_parent)
	{
		c_filename = p_parent.getFilename();
		c_dirToSearch = new ArrayList<SearchDirectory>();
		c_dirToSearch.add(p_parent.getDirToSearch());
		c_parent = p_parent;
		c_filesFound = new Vector<File>();
	}
	
	public File find()
	{
		return find(c_filename);
	}
	
	/*
	 * finds the file
	 */
	public File find(String p_filename)
	{
		c_filename = p_filename;
		
		c_threadList = new ArrayList<Thread>();
		
		/*
		 * Following code is for thread driven search
		 *
		//starts a thread for each directory in the paths array
		for(int i = 0; i < c_dirToSearch.size(); i++)
		{
			Thread l_thread = new Thread(new FindFile(this));
			l_thread.start(); 
			
			c_threadList.add(l_thread);
		}
		
		while(true)
		{
			if(c_isConfigFound)
			{
				for(ListIterator<Thread> l_it = c_threadList.listIterator(); l_it.hasNext(); )
				{
					l_it.next().interrupt(); 
					l_it.remove();
				}
				
				synchronized (c_fileFound)
				{
					return c_fileFound; 
				}
			}
		}
		*/
		while(!c_isConfigFound && c_dirToSearch.size() != 0)
			searchNextDir(); 
		
		if(c_isConfigFound)
			return c_filesFound.get(0);
		else
			return null;
			
		
	}
	
	public Vector<File> findMultiple()
	{
		return findMultiple(c_filename);
	}
	
	public Vector<File> findMultiple(String p_filename)
	{
		c_filename = p_filename;
		c_findMultiple = true;
		
		c_threadList = new ArrayList<Thread>();
		
		while(c_dirToSearch.size() != 0)
			searchNextDir(); 
		
		if(c_isConfigFound)
			return c_filesFound;
		else
			return null;
	}
	
	public Thread findAsync(AsyncFindListener p_finder)
	{
		c_finder = p_finder;
		c_findMultiple = true;
		
		this.start();
		return this;
	}
	
	public synchronized void setFileFound(File p_fileFound)
	{
		c_filesFound.add(p_fileFound);
		c_isConfigFound = true;
	}
	
	public synchronized String getFilename()
	{
		return c_filename; 
	}
	
	public synchronized SearchDirectory getDirToSearch()
	{
		if(c_dirToSearch.size() != 0)
			return c_dirToSearch.remove(0);
		
		return null;
	}
	
	/* (non-Javadoc)
	 * @see java.lang.Runnable#run()
	 */
	public void run()
	{
		/*while(c_dirToSearch.size() != 0 && (c_findMultiple || !c_isConfigFound))
		{
			searchNextDir(); 
			
			if(c_dirToSearch.size() == 0)
			{
				SearchDirectory l_search = c_parent.getDirToSearch();
				File l_dir = l_search.directory;
				
				if(l_dir == null)
					return;
				else
					c_dirToSearch.add(new SearchDirectory(l_search.depth, l_dir));
			}
		}*/
		while( c_dirToSearch.size() != 0 )
			searchNextDir();
	}
	
	private void determineOS()
	{
		c_osname = System.getProperty("os.name");
	}
	
	private void getPathsToSearch()
	{	
		String[] l_paths = null; 
		
		if(c_osname.equals(FindFileConst.LINUX_NAME))
		{
			l_paths = FindFileConst.LINUX_MOUNTS;
		}
		else if(c_osname.equals(FindFileConst.MAC_OSX_NAME))
		{
			l_paths = FindFileConst.MAC_MOUNTS;
		}
		
		for(int i = 0; i < l_paths.length; i++)
		{
			c_dirToSearch.add(new SearchDirectory(0, new File(l_paths[i])));
		}
	}
	
	private void searchNextDir()
	{
		SearchDirectory l_search = c_dirToSearch.remove(0);
		File l_file = l_search.directory;
		
		//get the listing of directories and files in current dir
		String[] l_currDirList = l_file.list(); 
		
		//TODO: make this an exception
		if(l_currDirList == null)
			return;
		
		for(int i = 0; i < l_currDirList.length; i++)
		{
			File l_tempFile = new File(l_file.getPath() + System.getProperty("file.separator") + l_currDirList[i]);
			
			if(l_tempFile.isFile())
			{	
				if( c_pattern == null )
				{
					if(l_tempFile.getName().equals(c_filename))
					{
						setFileFound(l_tempFile);
						if( !c_findMultiple )
							return;
					}
				}
				else
				{
					if( c_pattern.matcher(l_tempFile.getName()).matches() )
					{
						if( c_finder != null )
							c_finder.report(l_tempFile);
						else
							setFileFound(l_tempFile);
						if( !c_findMultiple )
							return;
					}
				}
			}
			else if(l_tempFile.isDirectory())
			{
				//push the directory on the directories to search stack 
				if( l_search.depth <= c_recurseDepth || c_recurseDepth < 0 )
				{
					c_dirToSearch.add(0, new SearchDirectory(l_search.depth + 1, l_tempFile));
				}
			}	
		}
	}
}
