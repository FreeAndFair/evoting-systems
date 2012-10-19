/*
 * @(#)TallyMethod.java
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

/**
 * TallyMethod is an abstract class or Interface that defines the functions
 * a voting method needs to implement in order to work with the rest of the
 * scantegrity applications.
 * 
 * This should be generalized enough to support PluralityTally, Ranked Choice, Score
 * Voting, MultiWinner Elections, etc. Part of that support is the "log" and
 * "listing candidate rankings." The latter should include a rank that could be
 * a percentage (If Necessary), which is why it is represented as a String. 
 *
 * We chose this particular design to enable generic programs to be written to
 * display the data in as many formats as possible. Most applications will only
 * call one of these to get the data in the format they need.
 * 
 * The intended usage is for the application to get the configuration and use it
 * to determine the method type and (possibly) data format. Then it can feed
 * the data to the TallyMethod, which validates and calculates results. Thus,
 * we expect a config class to be able to return properly configured objects 
 * that implement the TallyMethod interface and the user of these methods
 * will simply send them (currently only) dark mark logic matrices of the 
 * results they parsed, scanned, or otherwise obtained.
 * 
 * @author Richard Carback
 * @version 0.0.1 
 * @date 24/02/09
 */

package org.scantegrity.common.methods;

import java.util.TreeMap;
import java.util.Vector;

import org.scantegrity.common.Ballot;
import org.scantegrity.common.Contest;
import org.scantegrity.common.Logging;
import org.scantegrity.common.methods.ContestChoice;
import org.scantegrity.common.methods.ContestResult;

public interface TallyMethod {
	/* TODO: It might turn out that this is better done through abstract
	 * classes, but that's indeterminate at this time.
	 */

	/**
	 * validateBallot checks a ballot and returns a map of possible
	 * choices and if those choices were read.
	 */
	TreeMap<String, String> validateContest(int p_contestId, Ballot p_ballot);
	
	/**
	 * Tally - tells the method to take the current data set and
	 * calculate results from it. This may throw exceptions if the format
	 * of a ballot is invalid. It's assumed at this point in time that the
	 * ballot data will be in darkmark logic (0 for unmarked, 1 for marked).
	 * 
	 * One key fact to note: Every ballot is assumed to be normalized, and this 
	 * gets rid of the need for the style mapping of contestantIDs. In other
	 * words, contestant 0 in one ballot is the same contestant in all
	 * ballots!
	 * 
	 * @param p_ballots an array of 2 dimensional darkmark logic contest 
	 * results.  
	 */
	ContestResult tally(Contest p_contest, Vector<ContestChoice> p_ballots);

	/**
	 * This method checks the given contest data to verify that there 
	 * are no voting errors that will require human verification of the 
	 * votes in the ERM. If there are errors (such as Overvotes 
	 * or Undervotes as in IRV) then we will have to save the ballot image have 
	 * the election judge manually process the ballot in the ERM like we do 
	 * with Write-Ins. 
	 * @param c_log 
	 * 
	 * @param Integer[][] p_contest_data: The contest data in 2d array of contestant id and 
	 * actual ballot marks. 
	 * @param Vector<String> p_error_condition: String error condition where we will save the 
	 * error condition we find if any. 
	 * 
	 * @return boolean: If an error condition is found. 
	 */
	boolean hasVotingErrors(Integer[][] l_contest_data, Vector<String> l_error_conditions, Logging c_log);
	
	
}