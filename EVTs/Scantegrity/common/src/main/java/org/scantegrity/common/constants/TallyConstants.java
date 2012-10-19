/*
 * @(#)TallyConstants.java.java
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
 */
public class TallyConstants
{
	/**
	 * Vote Recording Constants
	 * These are here so the gui can check the string 
	 * on how the vote was counted or not or overvoted.
	 */
	
	public static final String NO_VOTE = "No Vote";
	public static final String VOTE_RECORDED = "Vote Recorded";
	public static final String OVERVOTE = "Multiple Candidates Recorded";
	public static final String OVERVOTE_ROW = "Multiple Ranks Recorded for Same Candidate";
}
