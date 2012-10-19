/*
 * @(#)FindFileConst.java.java
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
package org.scantegrity.common.constants;

/**
 * @author John Conway
 * 
 * Holds the constants for the FindFile Utility in 
 * lib.
 */
public class FindFileConst
{
	/*
	 * OS Names
	 */
	public static final String LINUX_NAME = "Linux";
	
	//MAC
	public static final String MAC_OSX_NAME = "Mac OS X";
	public static final String MAC_OS_NAME = "Mac OS";
	
	//Windows
	public static final String WINDOWS_2000_NAME = "Windows 95";
	public static final String WINDOWS_XP_NAME = "Windows XP";
	public static final String WINDOWS_2003_NAME = "Windows 2003"; 
	
	
	/*
	 * Linux Default Folders 
	 * 
	 * Note: Each string in the array is in order of priority.
	 */
	public static final String[] LINUX_MOUNTS = {"/media/","/mnt/"};
	
	/*
	 * Windows Default Folders
	 */
	public static final String[] WINDOWS_MOUNTS = {};
	
	/*
	 * Mac Default Folders
	 */
	public static final String[] MAC_MOUNTS = {"/VOLUMES/"};
}
