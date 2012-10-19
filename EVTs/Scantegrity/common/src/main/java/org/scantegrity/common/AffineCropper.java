/*
 * @(#)AffineCropper.java.java
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

import java.awt.Rectangle;
import java.awt.geom.AffineTransform;
import java.awt.geom.Point2D;
import java.awt.image.AffineTransformOp;
import java.awt.image.BufferedImage;
import java.io.File;
import java.io.IOException;

import javax.imageio.ImageIO;

/**
 * Utility class for cropping into a new image using an Affine Transform.
 * 
 * @author Richard Carback
 *
 */
@SuppressWarnings("unused")
public class AffineCropper
{
	static int i = 0; 
	/**
	 * Takes a rectangle in the expected space and pulls it from a scanned
	 * image given a specific AffineTransformOp. 
	 * @param p_src
	 * @param p_op
	 * @param p_bounds
	 * @return
	 * @throws Exception
	 */
	public static BufferedImage crop(BufferedImage p_src, 
			AffineTransformOp p_op, Rectangle p_bounds) throws Exception
	{
		
		//p_bounds = new Rectangle(0, 0, 2550, 3300);
		BufferedImage l_res = new BufferedImage(p_bounds.width,
												p_bounds.height,
												p_src.getType());
		Point2D.Double l_srcPt = new Point2D.Double();
		Point2D.Double l_dstPt = new Point2D.Double();
		AffineTransformOp l_op = new AffineTransformOp(p_op.getTransform().createInverse(), AffineTransformOp.TYPE_BILINEAR);
		int l_rgb;
		for (int l_i = 0; l_i < p_bounds.width; l_i++) 
		{
			for (int l_j = 0; l_j < p_bounds.height; l_j++)
			{
				try {
					l_srcPt.setLocation(p_bounds.getX()+l_i, p_bounds.getY()+l_j);
					l_op.getPoint2D(l_srcPt, l_dstPt);
					//System.out.print(l_srcPt.x + ", " + l_srcPt.y + " to ");
					//System.out.println(l_dstPt.x + ", " + l_dstPt.y);
					l_rgb = p_src.getRGB((int)Math.round(l_dstPt.x), 
										(int)Math.round(l_dstPt.y));
					l_res.setRGB(l_i, l_j, l_rgb);
				} catch (ArrayIndexOutOfBoundsException e) {} 
			}
		}
		/* BEGIN DEBUG * /
		try {
			ImageIO.write(l_res,"png",new File("code" + i + ".png"));
		} catch (IOException e) {
			e.printStackTrace();
		}		
		
		i++; 
		/* END DEBUG */
		return l_res;
	}
	
	
	/**
	 * Does the same thing as crop, but leaves it in the scaled of the src
	 * image instead of scaling up or down to meet a desired size.
	 * 
	 * @param p_src
	 * @param p_op
	 * @param p_bounds
	 * @return
	 * @throws Exception
	 */
	public static BufferedImage cropUnscaled(BufferedImage p_src, 
			AffineTransformOp p_op, Rectangle p_bounds) throws Exception
	{
		AffineTransform l_tran, l_inv;
		l_tran = p_op.getTransform(); 	//Detected -> Ideal
		l_inv = l_tran.createInverse(); //Ideal -> Detected
		AffineTransformOp l_invOp;
		l_invOp = new AffineTransformOp(l_inv, AffineTransformOp.TYPE_BILINEAR);
		
		//p_bounds is in the ideal space, we need it in the ideal space, BUT,
		//at the detected scale -- weird. 
		Rectangle l_bounds = new Rectangle(p_bounds);
		//Scale height and width down
		l_bounds.width *= Math.abs(l_inv.getScaleX());
		l_bounds.height *= Math.abs(l_inv.getScaleY());
		
		BufferedImage l_res;
		l_res = new BufferedImage(l_bounds.width,
				l_bounds.height,
				p_src.getType());		
		
		Point2D.Double l_idealPt = new Point2D.Double();
		Point2D.Double l_detPt = new Point2D.Double();
		int l_rgb;
		for (int l_i = 0; l_i < l_bounds.width; l_i++) 
		{
			for (int l_j = 0; l_j < l_bounds.height; l_j++)
			{
				try {
					//Scale the ideal points to get the next point at the 
					//detected scale. Scale sample up
					l_idealPt.setLocation(l_i*Math.abs(l_tran.getScaleX()), 
										l_j*Math.abs(l_tran.getScaleY()));
					//Use ideal offset
					l_idealPt.x += l_bounds.getX();
					l_idealPt.y += l_bounds.getY();
					
					l_invOp.getPoint2D(l_idealPt, l_detPt);
					//System.out.print(l_srcPt.x + ", " + l_srcPt.y + " to ");
					//System.out.println(l_dstPt.x + ", " + l_dstPt.y);
					l_rgb = p_src.getRGB((int)Math.round(l_detPt.x), 
										(int)Math.round(l_detPt.y));
					l_res.setRGB(l_i, l_j, l_rgb);
				} catch (ArrayIndexOutOfBoundsException e) {} 
			}
		}
		/* BEGIN DEBUG * /
		try {
			ImageIO.write(l_res,"png",new File("serial" + i + ".png"));
		} catch (IOException e) {
			e.printStackTrace();
		}		
		
		i++; 
		/* END DEBUG */
		return l_res;
	}	

}
