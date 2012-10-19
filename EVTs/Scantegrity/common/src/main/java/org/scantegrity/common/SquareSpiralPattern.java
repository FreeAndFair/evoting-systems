/*
 * @(#)SquareSpiralPattern.java.java
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

import java.awt.Point;
import java.util.NoSuchElementException;

/**
 * Generates a Square spiral search pattern. Useful for finding the alignment
 * marks on a scanned image.
 * 
 * @author Richard Carback
 *
 */
public class SquareSpiralPattern
{
	//Current x,y location in grid.
	private Point c_loc;
	
	//Size of the grid (e.g. when to tell if the spiral pattern stops.)
	private Integer c_size;
	
	//Current max and min
	private Integer c_max, c_min;
	
	private boolean c_right, c_down, c_empty;
	
	/**
	 * Create a new spiral pattern object of size 10.
	 */
	public SquareSpiralPattern() {
		this(10);
	}

	
	/**
	 * Create a new spiral pattern object.
	 * @param p_size The width of the box you need. Must be even, or the 
	 * last row and column will be ignored!
	 */
	public SquareSpiralPattern(Integer p_size) {
		c_size = p_size;
		c_max = 1;
		c_min = -1;
		c_right = true;
		c_down = true;
		c_loc = new Point(0,0);		
	}
	
	/**
	 * Get the next element coordinates.
	 * @return Location relative to the center location of a grid.
	 * @throws NoSuchElementException
	 */
	public Point next() throws NoSuchElementException {
		//Can I go right?
		if (c_loc.x < c_max && c_right) {
			c_loc.move(c_loc.x+1, c_loc.y);
			if (c_loc.x >= c_max) c_right = false;
		}
		//Can I go down?
		else if (c_loc.y < c_max && c_down) {
			c_loc.move(c_loc.x, c_loc.y+1);
			if (c_loc.y >= c_max) c_down = false;			
		}
		//Can I go left?
		else if (c_loc.x > c_min && !c_right) {
			c_loc.move(c_loc.x-1, c_loc.y);
			//Pattern ends moving left, determine if i should stop
			if (c_loc.x <= -1*c_size/2+1 && c_max >= c_size/2) {
				c_empty = true;
			}
		}
		//Can I go up?
		else if (c_loc.y > c_min && !c_down) {
			c_loc.move(c_loc.x, c_loc.y-1);
			//Reset to start moving to the right again
			if (c_loc.y <= c_min) {					
				c_down = true;
				c_right = true;
				c_max++;
				c_min--;
			}
		}
		else throw new NoSuchElementException();
		
		
		return c_loc;
	}
	
	
	public boolean isEmpty() {
			return c_empty;
	}	

}
