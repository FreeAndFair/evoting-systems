/*
 * @(#)AlignmentMarkReader.java.java
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

import java.awt.Point;
import java.awt.image.BufferedImage;


/**
 * Interface for finding alignment marks. Alignment marks are expected to be
 * different types of shapes (Circles, Squares, etc). This moves (specialized) 
 * detection code out of the BallotReader classes.
 * 
 * @author Rickhard Carback 
 * 
 */
public abstract class AlignmentMarkReader
{	
	//Every mark reader needs to have an acceptable tolerance. This will vary
	//based on type.
	protected Double c_tolerance = .05;
	protected Double c_scale = 1.0;
		
	/**
	 * Find an alignment mark. By finding multiple marks, the calling class
	 * can determine the skew of the ballot and correct errors being sent to 
	 * the detection function.
	 * 
	 * @param p_img The image to process
	 * @param p_loc The expected location
	 * @return The actual location
	 * @throws ArrayIndexOutOfBoundsException
	 */
	public abstract Point findMark(BufferedImage p_img, Point p_loc) throws ArrayIndexOutOfBoundsException;

	/**
	 * @param tolerance the tolerance to set
	 */
	public void setTolerance(Double p_tolerance)
	{
		c_tolerance = p_tolerance;
	}
	/**
	 * @return the tolerance
	 */
	public Double getTolerance()
	{
		return c_tolerance;
	}

	/**
	 * @return the scale
	 */
	public Double getScale()
	{
		return c_scale;
	}

	/**
	 * @param p_scale the scale to set
	 */
	public void setScale(Double p_scale)
	{
		c_scale = p_scale;
	}
}
