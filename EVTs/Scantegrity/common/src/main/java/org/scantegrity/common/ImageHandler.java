package org.scantegrity.common;

import java.awt.image.BufferedImage;

/************************************************************************
 * Provides callback interface for handling images loaded by ImageLoader
 * 
 * @author Travis
 *
 *************************************************************************/

public interface ImageHandler {
	
	public Ballot handleImage(BufferedImage p_image);

}
