/*
 * @(#)CircleAlignmentMarkReader.java.java
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

import java.awt.Color;
import java.awt.Graphics2D;
import java.awt.Point;
import java.awt.image.BufferedImage;
import java.io.File;
import java.io.IOException;

import javax.imageio.ImageIO;

import org.scantegrity.common.DetectBlack;
import org.scantegrity.common.SquareSpiralPattern;

/**
 * @author Richard Carback
 *
 */
public class CircleAlignmentMarkReader extends AlignmentMarkReader
{
	private Integer c_radius = 25;
	
	public CircleAlignmentMarkReader()
	{
		super();
		c_radius = 25;
	}
	
	/**
	 * @param c_radius the radius of the circle
	 */
	public CircleAlignmentMarkReader(Integer p_radius)
	{
		super();
		c_radius = p_radius;
	}	

	
	/**
	 * @param c_radius the radius of the alignment mark circle
	 * @param p_tolerance the tolerance level.
	 */
	public CircleAlignmentMarkReader(Integer c_radius, Double p_tolerance)
	{
		this(c_radius);
		c_tolerance = p_tolerance;
	}	
		
	/**
	 * Returns the center of the circle given p_loc as the expected position.
	 * Assumes circle is black. Won't exceed tolerance level in search. Uses
	 * the radius defined globally.
	 * @param p_img the Image to search
	 * @param p_loc the starting location
	 * @return the center of the circle, or null if it could not be found.
	 */
	public Point findMark(BufferedImage p_img, 
			Point p_loc) throws ArrayIndexOutOfBoundsException
	{
		Point l_cur = new Point(p_loc);
		Point l_res = new Point(l_cur);
		Point l_next;
		//Scale our parameters
		Integer l_radius = (int)(c_radius*c_scale);
		//System.out.println("Scaled Radius:" + l_radius);

		//Search space is %tolerable/radius
		Integer l_search = (int)(getTolerance()*p_img.getWidth()/l_radius);
		//System.out.println("Size of search space:" + l_search);
		//..or at least 2 spots on each side of the starting point
		l_search = Math.max(l_search, 4);
		
		try {
			l_res = detectCircle(p_img, l_cur, l_radius);
		} catch (ArrayIndexOutOfBoundsException l_e) {}
		
		/* The mark could be on the opposing corner, we check both in turn.
		 * 
		 */
		Point l_inv = new Point();
		l_inv.x = p_img.getWidth() - p_loc.x;
		l_inv.y = p_img.getHeight() - p_loc.y;
		try {
			l_res = detectCircle(p_img, l_inv, l_radius);
		} catch (ArrayIndexOutOfBoundsException l_e) {}		
		
		
		SquareSpiralPattern l_spiral = new SquareSpiralPattern(l_search);
		while (l_res == null && !l_spiral.isEmpty())
		{
			//System.out.println("Did not find on first try, keep going...");
			l_next = l_spiral.next();

			//NOTE: We might be able to jump by Diameter, that would speed up
			//the process. A factor like 1.5 is more likely, because there is
			//whitespace on each end and you don't want to accidentally jump
			//a whole alignment mark! (consider a grid of circles, and you will
			//be jumping between them into the whitespace of each).
			//TODO: Needs greater math-fu behind it.
			l_cur.setLocation(l_next.x*l_radius + p_loc.x, 
								l_next.y*l_radius + p_loc.y);
			l_inv.setLocation(p_img.getWidth() - (l_next.x*l_radius+p_loc.x),
							   p_img.getHeight() - (l_next.y*l_radius+p_loc.y));

			
			//System.out.println("Trying: " + l_cur.x + ", " + l_cur.y);
			try {
				l_res = detectCircle(p_img, l_cur, l_radius);
			} catch (ArrayIndexOutOfBoundsException l_e) {}
			
			//Try inverted position
			if (l_res == null)
			{
				try {
					//System.out.println("Trying: " + l_inv.x + ", " + l_inv.y);					
					l_res = detectCircle(p_img, l_inv, l_radius);
					
					
				} catch (ArrayIndexOutOfBoundsException l_e) {}
			}
			/* BEGIN DEBUG * / 
		//NOTE: This will sometimes break scanning, because the square created
		// will be in the right spot to make it think it's in a big blob o'black  
			try {
				BufferedImage l_img = p_img.getSubimage(0, 0, p_img.getWidth(),
														p_img.getHeight());
				Graphics2D l_out = l_img.createGraphics();
				l_out.setColor(Color.BLACK);
				l_out.fillRect(l_inv.x, l_inv.y, 5, 5);
				l_out.fillRect(l_cur.x, l_cur.y, 5, 5);
				ImageIO.write(l_img,"png",new File("test.png"));
			} catch (IOException e) {
				e.printStackTrace();
			}						
			/* END DEBUG */
		}
		return l_res;
	}

	/**
	 * Detects if the given point belongs to a circle.
	 * @param p_img The current image.
	 * @param p_point the location of the point.
	 * @return the center of the circle or null if the point was not in a circle
	 * @throws ArrayIndexOutOfBoundsException
	 */
	protected Point detectCircle(BufferedImage p_img, Point p_point, 
			int p_radius) throws ArrayIndexOutOfBoundsException
	{
		//Gratuitous Bounds Check
		if (p_point.x < 0 || p_point.x > p_img.getWidth() 
			|| p_point.y < 0 || p_point.y > p_img.getHeight())
		{
			//System.out.println("OOB!");
			return null;
		}
		
		Point l_c = null;		
		//If we hit, see where we are in relation to the center
		if (DetectBlack.isBlack(p_point.x, p_point.y, p_img)) {
			Integer l_lx, l_rx, l_uy, l_dy;
			l_lx = l_rx = p_point.x;
			l_uy = l_dy = p_point.y;
			for (int l_i = 0; l_i < p_radius*2; l_i++) {
				//NOTE: These stop moving when they hit whitespace, if the 
				//Alignment mark is not contiguouse, this can cause a problem!
				//Left
				if (l_lx-1 > 0 
						&& DetectBlack.isBlack(l_lx-1, p_point.y, p_img)) {
					l_lx--;
				}
				//Right
				if (l_rx+1 < p_img.getWidth() 
						&& DetectBlack.isBlack(l_rx+1, p_point.y, p_img)) {
					l_rx++;
				}
				//Up
				if (l_uy-1 > 0 
						&& DetectBlack.isBlack(p_point.x, l_uy-1, p_img)) {
					l_uy--;
				}
				//Down
				if (l_dy+1 < p_img.getHeight()
						&& DetectBlack.isBlack(p_point.x, l_dy+1, p_img)) {
					l_dy++;
				}
			}
			//a possible center point
			Double l_cy = (l_dy - l_uy)/2.0 + l_uy;
			Double l_cx = (l_rx - l_lx)/2.0 + l_lx;
			l_c = new Point();
			l_c.setLocation(l_cx, l_cy);
			//System.out.println("Hit: possible center is :" + l_c.x +", " + l_c.y);
			
			//TODO: The following block might not really be necessary at all.
			//Is the radius we think we know consistant and close enough?
			Double l_d[] = new Double[4];
			l_d[0] = l_c.distance(l_lx, p_point.y);
			l_d[1] = l_c.distance(l_rx, p_point.y);
			l_d[2] = l_c.distance(p_point.x, l_uy);
			l_d[3] = l_c.distance(p_point.x, l_dy);
			//Detect if it is probably not a circle
			//double tolerance here, because the next routine will really
			//determine if it's a circle! Could be up to 5 pixels off anyway!
			for (int l_i = 0; l_i < 4; l_i++)
			{
				if (Math.abs(l_d[l_i] - p_radius) 
						> Math.max(2*p_radius*getTolerance(), 5)) {
					//System.out.println("Probably not a circle");
					return null;
				}
				//System.out.println(l_d[l_i]);
			}
			
			//probably a circle, but might not be 
			int l_i;
			Point l_tmp = new Point();
			Double l_rad = 45.0; //Radians
			Double l_ed = 5.0; //Tolerable edge distance
			//System.out.println("l_ed: " + l_ed);
			Integer l_edx, l_edy;
			for (l_i = 0; l_i < 360/l_rad; l_i++)
			{			
				//Check for a circle, x = r*cos(t), y = r*sin(t)
				//45 is 360/8 Math.cos takes a radian, we do an 8 point check
				double l_x = p_radius*Math.cos(l_i*l_rad)+l_c.x;
				double l_y = p_radius*Math.sin(l_i*l_rad)+l_c.y;
				l_tmp.setLocation(l_x, l_y);
				
				//Go out or in depending if we hit again.
				l_edx = (int)Math.ceil(l_ed*Math.cos(l_i*l_rad));
				l_edy = (int)Math.ceil(l_ed*Math.sin(l_i*l_rad));
				//System.out.println("Checking for black: " + (l_tmp.x - l_edx) + ", " + (l_tmp.y - l_edy));
				if (!DetectBlack.isBlack(l_tmp.x, l_tmp.y, p_img)) {
					//System.out.println("No Black Out");
					//We didn't hit, check inward.
					if (!DetectBlack.isBlack(l_tmp.x - l_edx, l_tmp.y - l_edy, p_img))
					{
						//System.out.println("No Black Inward");
						return null;
					}
				} else {
					//We did hit, make sure it's not just a giant blob of ink!
					if (DetectBlack.isBlack(l_tmp.x + l_edx, l_tmp.y + l_edy, p_img))
					{
						//System.out.println("Giant Blob!");
						return null;
					}
				}
			}
		}
		
		return l_c;
	}

	/**
	 * @param radius the radius to set
	 */
	public void setRadius(Integer p_radius)
	{
		c_radius = p_radius;
	}


	/**
	 * @return the radius
	 */
	public Integer getRadius()
	{
		return c_radius;
	}

	
	
	
}
