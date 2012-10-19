/*
 * @(#)ScannerConfig.java
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

import java.util.Vector;
import java.util.logging.Level;

import org.scantegrity.common.BallotStyle;
import org.scantegrity.common.Contest;

/**
 * ScannerConfig represents the configuration needed for the scanner in an 
 * election. This information is read from an XML file and this class is used
 * to retrieve objects needed by the Scanner application on demand. 
 * 
 * In particular, ScannerConfig tracks the polling place information, and 
 * also contains the class configurations necessary to decode each contest based 
 * on ballot style and report results at the end of the day.
 * 
 * Future work for this class: 
 * 	-methods for accessing scanner information stored in Crypto Hardware 
 *  -multiple polling place information to "detect" location based on chief 
 *   judge?
 *  
 *  
 * @author Richard Carback
 * @version 0.0.1 
 * @date 07/03/09
 */
public class ScannerConfig {
	/**
	 * TODO: Needs to add authentication for chief judge and possibly the 
	 * other judge pins. 
	 */
	private int c_pollID = -1;
	private int c_scannerID = -1;
	private String c_name = "Unknown Name";
	private String c_location = "Unknown Location";
	private String c_date = "Unknown Date"; //Date and time are stored here.
	private String c_time = "Unknown Time";
	private String c_logName = null;
	private Level c_logLevel = Level.ALL;
	private Vector<String> c_chiefJudges = null;
	private Vector<String> c_judgePassHash = null;
	private BallotReader c_reader = null;
	private Vector<Contest> c_contests = null;
	protected Vector<BallotStyle> c_styles = null;
	private Vector<String> c_outputDirNames = null;
	private String c_errDir = null;
	private String c_countFileName = null;
	
	public ScannerConfig() {
		c_pollID = -1;
		c_scannerID = -1;
		c_name = "Unknown Name";
		c_location = "Unknown Location";
		c_date = "Unknown Date"; //Date and time are stored here.
		c_time = "Unknown Time";
		c_logName = null;
		c_logLevel = Level.ALL;
		c_chiefJudges = new Vector<String>();
		c_chiefJudges.add("Unknown Chief Judge");
		c_judgePassHash = new Vector<String>();
		c_judgePassHash.add("");
		c_reader = new ScantegrityBallotReader();
		c_contests = new Vector<Contest>();
		c_styles = new Vector<BallotStyle>();	
		c_outputDirNames = new Vector<String>();
		c_errDir = "";
		c_countFileName = "";
	}

	/**
	 * @return the pollID
	 */
	public int getPollID() {
		return c_pollID;
	}

	/**
	 * @param p_pollID the pollID to set
	 */
	public void setPollID(int p_pollID) {
		c_pollID = p_pollID;
	}

	/**
	 * @return the scannerID
	 */
	public int getScannerID() {
		return c_scannerID;
	}

	/**
	 * @param p_scannerID the scannerID to set
	 */
	public void setScannerID(int p_scannerID) {
		c_scannerID = p_scannerID;
	}

	/**
	 * @return the name
	 */
	public String getName() {
		return c_name;
	}

	/**
	 * @param p_name the name to set
	 */
	public void setName(String p_name) {
		c_name = p_name;
	}

	/**
	 * @return the location
	 */
	public String getLocation() {
		return c_location;
	}

	/**
	 * @param p_location the location to set
	 */
	public void setLocation(String p_location) {
		c_location = p_location;
	}

	/**
	 * @return the date
	 */
	public String getDate() {
		return c_date;
	}

	/**
	 * @param p_date the date to set
	 */
	public void setDate(String p_date) {
		c_date = p_date;
	}

	/**
	 * @return the time
	 */
	public String getTime() {
		return c_time;
	}

	/**
	 * @param p_time the time to set
	 */
	public void setTime(String p_time) {
		c_time = p_time;
	}

	/**
	 * @return the logName
	 */
	public String getLogName() {
		return c_logName;
	}

	/**
	 * @param p_logName the logName to set
	 */
	public void setLogName(String p_logName) {
		c_logName = p_logName;
	}

	/**
	 * @return the logLevel
	 */
	public Level getLogLevel() {
		return c_logLevel;
	}

	/**
	 * @param p_logLevel the logLevel to set
	 */
	public void setLogLevel(Level p_logLevel) {
		c_logLevel = p_logLevel;
	}

	/**
	 * @return the chiefJudges
	 */
	public Vector<String> getChiefJudges() {
		return c_chiefJudges;
	}

	/**
	 * @param p_chiefJudges the chiefJudges to set
	 */
	public void setChiefJudges(Vector<String> p_chiefJudges) {
		c_chiefJudges = p_chiefJudges;
	}

	/**
	 * @return the judgePassHash
	 */
	public Vector<String> getJudgePassHash() {
		return c_judgePassHash;
	}

	/**
	 * @param p_judgePassHash the judgePassHash to set
	 */
	public void setJudgePassHash(Vector<String> p_judgePassHash) {
		c_judgePassHash = p_judgePassHash;
	}

	/**
	 * @return the reader
	 */
	public BallotReader getReader() {
		return c_reader;
	}

	/**
	 * @param p_reader the reader to set
	 */
	public void setReader(BallotReader p_reader) {
		c_reader = p_reader;
	}

	/**
	 * @return the contests
	 */
	public Vector<Contest> getContests() {
		return c_contests;
	}

	/**
	 * @param p_contests the contests to set
	 */
	public void setContests(Vector<Contest> p_contests) {
		c_contests = p_contests;
	}

	/**
	 * @return the styles
	 */
	public Vector<BallotStyle> getStyles() {
		return c_styles;
	}

	/**
	 * @param p_styles the styles to set
	 */
	public void setStyles(Vector<BallotStyle> p_styles) {
		c_styles = p_styles;
	}

	/**
	 * @return the outputDirNames
	 */
	public Vector<String> getOutputDirNames() {
		return c_outputDirNames;
	}

	/**
	 * @param p_outputDirNames the outputDirNames to set
	 */
	public void setOutputDirNames(Vector<String> p_outputDirNames) {
		c_outputDirNames = p_outputDirNames;
	}

	/**
	 * @return the errDir
	 */
	public String getErrDir() {
		return c_errDir;
	}

	/**
	 * @param p_errDir the errDir to set
	 */
	public void setErrDir(String p_errDir) {
		c_errDir = p_errDir;
	}

	public void setCountFileName(String p_countFileName) {
		c_countFileName = p_countFileName;
	}
	
	public String getCountFileName()
	{
		return c_countFileName;
	}



}

