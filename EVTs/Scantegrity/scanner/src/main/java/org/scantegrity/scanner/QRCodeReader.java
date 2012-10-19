/*
 * @(#)QRCodeReader.java.java
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

import java.awt.Rectangle;
import java.awt.image.AffineTransformOp;
import java.awt.image.BufferedImage;
import java.util.Hashtable;
import java.util.Vector;

import org.scantegrity.common.AffineCropper;

import com.google.zxing.BarcodeFormat;
import com.google.zxing.BinaryBitmap;
import com.google.zxing.DecodeHintType;
import com.google.zxing.MultiFormatReader;
import com.google.zxing.Result;
import com.google.zxing.client.j2se.BufferedImageLuminanceSource;
import com.google.zxing.common.HybridBinarizer;

/**
 * @author Richard Carback
 *
 */
public class QRCodeReader implements SerialNumberReader
{
	private Rectangle c_boundingBox = new Rectangle(144, 112, 278-144, 242-112);

	/* (non-Javadoc)
	 * @see org.scantegrity.scanner.SerialNumberReader#getSerialNumber(java.awt.image.BufferedImage)
	 */
	/**
	 * This method assumes that p_ballot is a properly rotated and bounded box.
	 * Since different barcode setups may require a whole ballot to process, it
	 * probably shouldn't do that.
	 */
	public String readSerial(BufferedImage p_img, AffineTransformOp p_op) 
	throws Exception
	{
		BufferedImageLuminanceSource l_serialImg;
		//int l_start = (int) System.currentTimeMillis();
		//System.out.println("Trying...");
		
		l_serialImg = new BufferedImageLuminanceSource(
					AffineCropper.cropUnscaled(p_img, p_op, c_boundingBox));
		//l_serial = new BufferedImageMonochromeBitmapSource(AffineCropper.crop(p_img, p_op, c_boundingBox));
		
		BinaryBitmap l_serialBitMap = new BinaryBitmap(
										new HybridBinarizer(l_serialImg));
		
		Vector<BarcodeFormat> l_formats = new Vector<BarcodeFormat>();
		l_formats.add(BarcodeFormat.QR_CODE);
		Hashtable<DecodeHintType, Object> hints = null;
		hints = new Hashtable<DecodeHintType, Object>(3);
		hints.put(DecodeHintType.TRY_HARDER, Boolean.TRUE);
		//hints.put(DecodeHintType.PURE_BARCODE, Boolean.TRUE);
		hints.put(DecodeHintType.POSSIBLE_FORMATS, l_formats);

		com.google.zxing.qrcode.QRCodeReader l_r = new com.google.zxing.qrcode.QRCodeReader();
		Result result = l_r.decode(l_serialBitMap, hints);
		
		
		//System.out.println("The Result: " + result.getText());
		//System.out.println("Serial Scan Time:" + (int)(System.currentTimeMillis()-l_start) + "ms");
		return result.getText();
	}
	
	public void setSerialBoundingBox(Rectangle p_boundingBox)
	{
		c_boundingBox = p_boundingBox;
	}
	
	public Rectangle getSerialBoundingBox()
	{
		return c_boundingBox;
	}

}
