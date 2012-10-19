/*
 * @(#)DrunkDriver.java
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

import java.awt.Color;
import java.awt.Point;
import java.awt.geom.Point2D;
import java.awt.image.BufferedImage;
import java.util.Random;

/**
 * Provides a utility to check if a page is blank.
 * 
 * @author Richard Carback
 *
 */
public class DrunkDriver
{
	private static Random c_prng = null;
	
	public static boolean isDrunk(BufferedImage p_img, int p_flips)
	{
		if (c_prng == null)
		{
			c_prng = new Random(System.currentTimeMillis());
		}
		
		//System.out.println(p_img.getHeight() + ", " + p_img.getWidth());
		Point l_pnt[] = new Point[6];
		l_pnt[0] = new Point(p_img.getWidth()/4, 0);
		l_pnt[1] = new Point(p_img.getWidth()/2, 0);
		l_pnt[2] = new Point(p_img.getWidth()*3/4, 0);
		l_pnt[3] = new Point(0, p_img.getHeight()/4);
		l_pnt[4] = new Point(0, p_img.getHeight()/2);
		l_pnt[5] = new Point(0, p_img.getHeight()*3/4);
		int l_dst[] = { 0, 0, 0, 0, 0, 0};
		int l_cnt[] = { 0, 0, 0, 0, 0, 0};
		int l_dir[] = { 0, 0, 0, 0, 0, 0};
		int l_basex = p_img.getWidth()/4;
		int l_basey = p_img.getHeight()/4;
		boolean l_pre[] = { false, false, false, false, false, false };
		
		int l_i = 0;
		int l_max = Math.max(p_img.getHeight(), p_img.getWidth());
		
		while (l_i < l_max)
		{			
			int l_b = l_basex;
			Point2D.Double l_tmp = new Point2D.Double();
			for (int l_j = 0; l_j < 6; l_j++)
			{
				if (l_j == 3) l_b = l_basey;

				int l_t = c_prng.nextInt(2) - 1;
				if (l_dir[l_j] == 0) l_dir[l_j] = l_t;
				if (Math.abs(l_dst[l_j]) >= l_b/2) 
					l_dir[l_j] = (l_dst[l_j]>0) ? 1:-1;
				l_dst[l_j] += l_t*l_dir[l_j];
				
				if (l_j >= 3)
				{
					l_tmp.x = l_pnt[l_j].x;
					l_tmp.y = l_pnt[l_j].y + l_dst[l_j];					
					l_pnt[l_j].x++;
				}
				else
				{
					l_tmp.x = l_pnt[l_j].x + l_dst[l_j];
					l_tmp.y = l_pnt[l_j].y;
					l_pnt[l_j].y++;
				}
				//System.out.println(l_tmp);
				
				if (l_tmp.x < p_img.getWidth() && l_tmp.y < p_img.getHeight() 
						&& l_tmp.x > 0 && l_tmp.y > 0)
				{
					if ((DetectBlack.isBlack(l_tmp, p_img) ^ l_pre[l_j]))
					{
						//System.out.println("FLIP: " + l_j);
						l_cnt[l_j]++;
						l_pre[l_j] = DetectBlack.isBlack(l_tmp, p_img);
					}
					//p_img.setRGB((int)l_tmp.x, (int)l_tmp.y, Color.blue.getRGB());
				}
				if (l_cnt[l_j] >= p_flips) return false;
				
			}
			l_i++;
		}
		
		return true;
	}
	
}
