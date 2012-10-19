/*
 * @(#)DirectoryWatcher.java.java
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


/**
 * @author John Conway
 *
 */
public class DirectoryWatcher implements Runnable
{
	private String c_srcDir; 
	private String c_destDir;
	
	private ImageLoader c_loader;
	
	public DirectoryWatcher(String p_srcDir, String p_destDir, ImageLoader p_loader)
	{
		c_srcDir = p_srcDir; 
		c_destDir = p_destDir;
		c_loader = p_loader; 
	}
	
	public void run()
	{
		File l_srcDirectory = new File(c_srcDir);
		File l_destDirectory = new File(c_destDir);
		
		if( !l_srcDirectory.exists() || !l_destDirectory.exists() )
		{
			System.out.println("Directory could not be found");
			return;
		}
		
		while(true)
		{
			File[] l_files = l_srcDirectory.listFiles();
			if(l_files.length > 0)
			{
				for(int x = 0; x < l_files.length; x++ )
				{
					try
					{
						c_loader.loadImage(l_files[x], l_destDirectory);
					}
					catch (IOException e)
					{
						// TODO Auto-generated catch block
						e.printStackTrace();
					}
				}
			}
			
			try
			{
				Thread.sleep(50);
			}
			catch (InterruptedException e)
			{
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}
	}
}
