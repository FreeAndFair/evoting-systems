/*
 * @(#)ScanContest.java
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
 * ScanContest.java - Provides an interface for classes that wish to
 * process a ballot image and extract data from it.  
 * 
 * @author Travis Mayberry
 * @date 28/02/09
 */
package org.scantegrity.scanner;

import java.util.logging.Logger;

public interface ScanContest {
	
	
	/**
	 * setLogger - Sets the logging object being used
	 * 
	 * @param p_logger - The configured logger to use.
	 */
	void setLogger(Logger p_logger);
	
	/**
	 * setBallotGeometry - Sets the geometry to be expected for the scanned image
	 * 
	 * @param p_geometry - The new ballot geometry
	 */
	//void setBallotGeometry(BallotGeometry p_geometry);
	
	/**
	 * getSerial - Returns the serial number on the ballot.  Calls 
	 * 
	 * @return - Serial number of the ballot
	 */
	String getSerial();
	
	/**
	 * detectMarks - Will align the ballot based on alignment marks, detect the serial
	 * number and detect ballot marks.
	 * 
	 * @throws AlignmentException - Thrown if one or both of the alignment marks cannot be found
	 * @throws SerialNotFoundException - Thrown if the serial number of the ballot cannot be found or read
	 */
	//void detectMarks() throws AlignmentException, SerialNotFoundException;
	
	/**
	 * getMarks - Returns the ballot marks in the form of a three dimensional array of integers
	 * 
	 * @return - Ballot marks detected
	 */
	int[][][] getMarks();
	
	
	
	
}