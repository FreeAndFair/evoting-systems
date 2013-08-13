/**
  * This file is part of VoteBox.
  * 
  * VoteBox is free software: you can redistribute it and/or modify
  * it under the terms of the GNU General Public License version 3 as published by
  * the Free Software Foundation.
  * 
  * You should have received a copy of the GNU General Public License
  * along with VoteBox, found in the root of any distribution or
  * repository containing all or part of VoteBox.
  * 
  * THIS SOFTWARE IS PROVIDED BY WILLIAM MARSH RICE UNIVERSITY, HOUSTON,
  * TX AND IS PROVIDED 'AS IS' AND WITHOUT ANY EXPRESS, IMPLIED OR
  * STATUTORY WARRANTIES, INCLUDING, BUT NOT LIMITED TO, WARRANTIES OF
  * ACCURACY, COMPLETENESS, AND NONINFRINGEMENT.  THE SOFTWARE USER SHALL
  * INDEMNIFY, DEFEND AND HOLD HARMLESS RICE UNIVERSITY AND ITS FACULTY,
  * STAFF AND STUDENTS FROM ANY AND ALL CLAIMS, ACTIONS, DAMAGES, LOSSES,
  * LIABILITIES, COSTS AND EXPENSES, INCLUDING ATTORNEYS' FEES AND COURT
  * COSTS, DIRECTLY OR INDIRECTLY ARISING OUR OF OR IN CONNECTION WITH
  * ACCESS OR USE OF THE SOFTWARE.
 */

package votebox.middle.view;

import java.awt.image.BufferedImage;
import java.awt.image.PixelGrabber;
import java.io.File;
import java.io.IOException;

import javax.imageio.ImageIO;

import votebox.sdl.SDL;
import votebox.sdl.SWIGTYPE_p_SDL_Surface;

/**
 * Turns a file into an imag type that VoteboxSDLView can deal with.<BR>
 * Internally, it lazily converts that file to an SDL_Surface.<BR>
 * Failure to release() will result in memory-leaks.  NO ATTEMPT IS MADE TO CLEANUP AT OBJECT DESTRUCTION.
 * @author Montrose
 *
 */
public class VoteboxSDLImage implements IViewImage {
	private File _file = null;
	private SWIGTYPE_p_SDL_Surface _surface = null;
	
	private int _width = -1;
	private int _height = -1;
	
	/**
	 * Allocates a new VoteboxSDLImage.<BR>
	 * Conversion to an SDL_Surface does not take place at this point, but the path must be valid.
	 * @param path
	 */
	public VoteboxSDLImage(String path){
		path = path.replace('/', File.separatorChar);

		_file = new File(path);
		
		if(!_file.exists()){
			throw new RuntimeException("Attempted to allocate VoteSDLImage with non-existent file, "+_file);
		}//if
	}//VoteboxSDLImage

	/**
	 * Releases the underlying SDL_Surface, it it still exists.<BR>
	 * Attempts to access this image's properties will result in the<BR>
	 * re-conversion of the underlying file.
	 */
	public void release(){
		if(_surface != null){
			SDL.vbSDL_FreeSurface(_surface);
			_surface = null;
		}
	}
	
	/**
	 * @see votebox.middle.view.IViewImage#getHeight()
	 */
	public int getHeight() {
		if(_surface == null)
			convert();
		
		return _height;
	}

	/**
	 * @return an SDL_Surface, containing the underlying file's image data
	 */
	public Object getImage() {
		if(_surface == null)
			convert();
		
		return _surface;
	}

	/**
	 * @see votebox.middle.view.IViewImage#getWidth()
	 */
	public int getWidth() {
		if(_surface == null)
			convert();
		
		return _width;
	}

	/**
	 * Converts a file in the file system into an SDL_Surface internally.
	 * Subsequently used for blitting, etc.
	 */
	private void convert(){
		try{
			//Read in the file using Java's libraries, rather than SDL's
			BufferedImage img = ImageIO.read(_file);
			_width = img.getWidth();
			_height = img.getHeight();
			
			//Allocate a new RGBA surface
			_surface = SDL.Alloc_Surface(_width, _height);
			
			if(_surface == null)
				throw new RuntimeException("Error allocating SDLSurface");
			
			int[] pixels = new int[_width * _height];
			PixelGrabber grabber = new PixelGrabber(img, 0, 0, _width, _height, pixels, 0, _width);
			
			//Grab all the pixels in aarrggbb format
			boolean success = grabber.grabPixels();
			
			if(!success)
				throw new RuntimeException("VoteboxSDLImage grabPixels failed!");
			
			//Pass these pixels across to SDL one-by-one
			for(int y = 0; y < _height; y++)
				for(int x = 0; x < _width; x++){
					int pixel = pixels[y * _width + x];
					int a = (pixel >> 24) & 0xFF;
					int r = (pixel >> 16) & 0xFF;
					int g = (pixel >>  8) & 0xFF;
					int b = (pixel >>  0) & 0xFF;
					
					int result = SDL.Surface_Set_Pixel(x, y, _surface, a, r, g, b);
					
					if(result == -1)
						throw new RuntimeException("Error occurred while setting pixel on surface");
				}//for
			
			//Make sure that the changes stick to the surface before anyone tries to blit with it
			SDL.vbSDL_UpdateRect(_surface, 0, 0, _width, _height);
		}catch(IOException e){
			throw new RuntimeException("Unable to convert VoteboxSDLImage", e);
		}catch(InterruptedException f){
			throw new RuntimeException("Unable to convert VoteboxSDLImage", f);
		}
	}//convert
	
}
