/*
 * @(#)SerialNumberReader.java
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

/**
 * SerialNumberReader is an abstract class for processing ballot serial numbers. It is
 * assumed that the serial number on each ballot in a polling place is the same,
 * but there may be a different type used in different elections (human readable
 * v. barcode, etc). 
 * 
 * The primary purpose of this class is two fold: determine the serial number
 * and determine the ballot style. Implementing classes expect to receive a
 * full ballot image (because the serial number could be split up over different
 * sides of the ballot), and there is no geometric data being stored at this
 * level. 
 * 
 * Ballot style could be the most significant digits of the serial number, or it
 * could be located elsewhere on the ballot. It is also represented as a number
 * and a configuration class should be able to determine an appropriate reader
 * for the ballot based on that number.
 *  
 * @author Richard Carback
 * @version 0.0.1 
 * @date 11/03/09
 */

package org.scantegrity.scanner;

import java.awt.image.AffineTransformOp;
import java.awt.image.BufferedImage;

//public abstract class SerialNumberReader {
public interface SerialNumberReader {
	/**
	 * Return the serial number located in this ballot image.
	 * @param p_ballot A 2D normalized image of the ballot.
	 * @return an integer of the serial number.
	 * @throws Exception if the serial number is unreadable.
	 */
	abstract String readSerial(BufferedImage p_img, AffineTransformOp p_op) 
	throws Exception;

}