/*
 * @(#)DrunkDriverTest.java.java
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

import java.awt.image.BufferedImage;
import java.io.File;
import java.io.IOException;

import javax.imageio.ImageIO;
//import javax.media.jai.JAI;
//import javax.media.jai.PlanarImage;

import org.junit.Test;
import org.scantegrity.common.DrunkDriver;

/**
 * @author Richard Carback
 *
 */
public class DrunkDriverTest
{

	/**
	 * @param args
	 */
	@Test
	public void TestDrunkDriver()
	{
		/*
		try
		{
			PlanarImage l_pn = JAI.create("fileload", "testing/scanner/sample-images/Basic/blank4.tiff");
			BufferedImage l_img = l_pn.getAsBufferedImage();
			long l_start = System.currentTimeMillis();
			if (DrunkDriver.isDrunk(l_img, 10)) System.out.println("Blank");
			else System.out.println("Not Blank");
			System.out.println("Time: " + (System.currentTimeMillis()-l_start));
			
			ImageIO.write(l_img, "png", new File("gimmekeys.tiff"));
		}
		catch (IOException e)
		{
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		*/
	}

}
