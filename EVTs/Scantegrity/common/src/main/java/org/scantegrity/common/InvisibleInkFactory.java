/*
 * @(#)InvisibleInkFactory.java
 *  
 * Copyright (C) 2008 Scantegrity Project
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
import java.awt.Font;
import java.awt.Graphics2D;
import java.awt.Point;
import java.awt.RenderingHints;
import java.awt.font.FontRenderContext;
import java.awt.image.BufferedImage;
import java.awt.image.ComponentColorModel;
import java.awt.image.DataBuffer;
import java.awt.image.PixelInterleavedSampleModel;
import java.awt.image.Raster;
import java.awt.image.WritableRaster;
import java.awt.image.DataBufferFloat;
import java.security.SecureRandom;
import java.util.TreeMap;
import java.util.Vector;
import org.scantegrity.common.CMYKColorSpace;

import com.itextpdf.text.pdf.CMYKColor;
 
/**
 * Generates images to print text in reactive (yellow) and dummy (magenta) ink.
 * The images produced by this module are embedded into ballot files that are 
 * printed on an invisible ink-capable printer. It is straightforward to 
 * generate the images, but the module has a number of extra functions to 
 * make the printed ink harder to read under various lights and types of 
 * paper. 
 * 
 * CHANGELOG:
 *  0.6.0
 *  	- Symbol Map is now configurable. It is still not checked to make sure
 *  	  all calls use these symbols, but it will pregenerate bitmaps, and
 *  	  perform other tasks. 
 *  	- Cacheing is a bit smarter now, cacheing each symbol possibility
 *  	  in each position. This grants a performance benefit without a huge
 *        memory hit. 
 *      - The fixed-width property of fonts required for the inkerator is 
 *        now enforced, which can cause oddities with some fonts (effectively,
 *        extra space between characters). 
 * 	0.5.0 
 * 		- The sampling and painting method to add a grid has been replaced by 
 * 		  symbol mappings of the smallest font-size for that font.
 * 
 * @author Richard Carback
 * @version 0.5.0 
 * @date 10/16/09
 */
public class InvisibleInkFactory {

	static final String DEFAULT_SYMBOLS = "ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789";	
	
	private Font c_font;
	private int c_padding;
	private int c_fontSize = 12;
	private SecureRandom c_csprng;
	private CMYKColorSpace c_cs = new CMYKColorSpace();
	private CMYKColor c_defFontColor = null;
	private CMYKColor c_defBgColor = null;
	private boolean c_cache = false;
	private String c_symbols = DEFAULT_SYMBOLS;
	
	
	private float[] c_minFontColor = {0,0,0,0};
	private float[] c_maxFontColor = {0,1,0,0};
	private float[] c_minBgColor = {0,0,0,0};
	private float[] c_maxBgColor = {0,0,1,0};
	private float[] c_minMaskColor = {0,0,0,0};
	private float[] c_maxMaskColor = {1,0,0,0};	
	
	//The maps for each symbol.
	TreeMap<Character, boolean[][]> c_symbolMap = null; 
	//Cache of strings
	TreeMap<String, BufferedImage> c_stringCache = null;
	
	//The True ascent of the current font.
	private int c_txtAscent;
	
	/* Grid Options
	 * If these arrays are sized > 1, then it creates a pattern as it 
	 * pastes itself across the image.
	 */
	private Integer[] c_hGridSpace = { 1 };
	private Integer[] c_vGridSpace = { 1 };
	private Integer[] c_hGridSize = { 5 };
	private Integer[] c_vGridSize = { 5 };
	private CMYKColor c_gridColor = new CMYKColor(0,0,0,0);
	
	private Integer c_maxMapWidth = 0;
	private Integer c_maxMapHeight = 0;
	
	/**
	 * Default constructor for the class, which uses a 18pt Serif
	 * Font, 10 pixel padding, and block mode without any csprng stuff.   
	 */
	public InvisibleInkFactory () {
		this ("SanSerif", 10, 2, null);
	}
	
	/**
	 * Overloaded constructor for the standard constructor. Defaults csprng to 
	 * null.
	 */	
	public InvisibleInkFactory (String p_fontName, int p_fontSize, int p_pad) {
		this (p_fontName, p_fontSize, p_pad, null);
	}

	/**
	 * Standard constructor that allows user to set font, fontsize, padding,
	 * and optionally, a CSPRNG.
	 * 
	 * @param p_fontName - Name of the font, e.g. "Times New Roman".
	 * @param p_fontSize - Font Size
	 * @param p_pad - Padding around the font
	 * @param p_csprng - A cryptographically secure pseudo-random number 
	 * 					 generator
	 */
	public InvisibleInkFactory (String p_fontName, int p_fontSize, int p_pad,
			SecureRandom p_csprng) {

		c_font = new Font(p_fontName, Font.BOLD, p_fontSize);
		c_fontSize = p_fontSize;
		c_padding = p_pad;
		c_csprng = p_csprng;
		SetTrueAscent(DEFAULT_SYMBOLS);
		c_symbolMap = new TreeMap<Character, boolean[][]>();
		c_defFontColor = new CMYKColor(0, 1, 0, 0);
		c_defBgColor = new CMYKColor(0, 0, 1, 0);
		generateSymbolMap();
	}
	
	
	/**
	 * Generate an image using the current settings and specified text.
	 * @param p_txt
	 * @return A BufferedImage object with the specified text and padding.
	 */
	public BufferedImage getBufferedImage(String p_txt) 
	{
		if (p_txt.length() <= 0) return null; 
		BufferedImage[] l_syms = new BufferedImage[p_txt.length()];
		
		//Top, right, bottom left padding.
		int l_imgWidth = 0;
		int l_imgHeight = 0;
		String l_prefix = "";
		for (int i = 0; i < p_txt.length(); i++)
		{
			if (i == 0) l_prefix = "first-";
			else if (i > 0 && i < p_txt.length()) l_prefix = "mid-";
			else l_prefix = "left-";
			if (isCache() 
					&& c_stringCache.containsKey(l_prefix+p_txt.charAt(i)))
			{
				l_syms[i] = c_stringCache.get(l_prefix+p_txt.charAt(i));
			}
			else 
			{
				int t,r,b,l;
				t = c_padding;
				r = (i == p_txt.length()-1) ? c_padding : 0;  
				b = c_padding;
				l = (i == 0) ? c_padding : 0;
				
				boolean[][] l_map = getMapForSymbol(p_txt.charAt(i));
				l_map = addPaddingToBitMap(l_map, t, r, b, l);			
				l_syms[i] = createImageFromBitMap(l_map);
				if (isCache())
				{
					c_stringCache.put(l_prefix+p_txt.charAt(i), l_syms[i]);
				}
			}

			l_imgWidth += l_syms[i].getWidth();
		}
		l_imgHeight = l_syms[0].getHeight();
		

		//Draw the symbol images into this image.
		BufferedImage l_ret = createCMYKImage(l_imgWidth, l_imgHeight);
		int l_cWidth = 0;
	    float[] l_dbuf = ((DataBufferFloat) 
	    				   l_ret.getRaster().getDataBuffer()).getData();
		for (int i = 0; i < l_syms.length; i++)
		{
		    float[] l_sbuf = ((DataBufferFloat) 
		    				   l_syms[i].getRaster().getDataBuffer()).getData();
		    
		    int l_width = l_syms[i].getWidth();
		    int l_height = l_syms[i].getHeight();
		    // Note, add offset height * width if you want to offset on y axis.
		    int l_doff = l_cWidth*4;
		    int l_soff = 0;
		    for (int y = 0 ; y < l_height; y++) 
		    {
		        System.arraycopy(l_sbuf, l_soff , l_dbuf, l_doff, 
		        					l_syms[i].getWidth()*4);
		    	l_doff += l_ret.getWidth()*4;
		    	l_soff += l_width*4; 
		    }
			
			//l_g2d.drawImage(l_syms[i], null, l_cWidth, 0);
			l_cWidth += l_syms[i].getWidth();
		}
		
		//Get a map of combined symbols.
		//boolean[][] l_map = getSuperMap(p_txt);
				
		return l_ret;
	}
	
	
	/**
	 * Adds padding to an nxn bitmap of a symbol.
	 * 
	 * @param p_map
	 * @param p_t
	 * @param p_r
	 * @param p_b
	 * @param p_l
	 * @return
	 */
	private boolean[][] addPaddingToBitMap(boolean[][] p_map, int p_top, 
			int p_right,int p_bottom, int p_left) 
	{
		int l_newWidth = c_maxMapWidth + p_right + p_left;
		int l_newHeight = c_maxMapHeight + p_top + p_bottom;
		boolean[][] l_ret = new boolean[l_newWidth][l_newHeight];
		
		int l_wStrt = (int) (Math.round((c_maxMapWidth-p_map.length)/2.0)
							+ p_left);
		int l_hStrt = (int) (Math.round((c_maxMapHeight-p_map[0].length)))
							+ p_top;
		
		for (int i = 0; i < p_map.length; i++)
		{
			System.arraycopy(p_map[i], 0, l_ret[i+l_wStrt], l_hStrt, 
															p_map[0].length);
		}
		
		return l_ret;
	}
	
	private BufferedImage createImageFromBitMap(boolean[][] p_map)
	{
		if (p_map == null) return null;
		
		int l_mapWidth = p_map.length;
		int l_mapHeight = p_map[0].length;
		
		//Use the unit-dimensions to generate an image width/height.
		int l_imgWidth = 0;
		for (int l_i = 0; l_i < l_mapWidth; l_i++)
		{
			l_imgWidth += c_hGridSize[l_i%c_hGridSize.length];
			if (l_i+1 != l_mapWidth+1) 
				l_imgWidth += c_hGridSpace[l_i%c_hGridSpace.length];
		}
		int l_imgHeight = 0;
		for (int l_i = 0; l_i < l_mapHeight; l_i++)
		{
			l_imgHeight += c_vGridSize[l_i%c_vGridSize.length];
			if (l_i+1 != l_mapHeight)
				l_imgHeight += c_vGridSpace[l_i%c_vGridSpace.length];
		}
		
		//Create the image, use the map to determine magenta or cyan colors.
		BufferedImage l_ret;
		//Graphics2D l_g2d;
		l_ret = createCMYKImage(Math.round(l_imgWidth), Math.round(l_imgHeight));		
		//l_g2d = l_ret.createGraphics();
		//imgx/imgy represent the current x and y offsets for the whole image.
		int l_imgx = 0;
		int l_imgy = 0;
		for (int l_x = 0; l_x < l_mapWidth; l_x++)
		{
			//Reset imgy to top of image.
			l_imgy = 0;
			for (int l_y = 0; l_y < l_mapHeight; l_y++)
			{
				float[] l_color = null;
				//The default is the background, we will try to find font colors.
				if (p_map[l_x][l_y])
				{
					l_color = getRandomFontColor();					
				}
				else
				{
					l_color = getRandomBgColor();
				}
				
				l_color = AddMask(l_color);
				
				//Draw the box
				int l_width = c_hGridSize[l_x%c_hGridSize.length];
				int l_height = c_vGridSize[l_y%c_vGridSize.length];
				CMYKColor l_c = new CMYKColor(l_color[0], l_color[1], 
												l_color[2], l_color[3]);
				//l_g2d.setColor(l_c);
				//l_g2d.fillRect(l_imgx, l_imgy, l_width, l_height);
				fillRect(l_ret, l_c, l_imgx, l_imgy, l_width, l_height);
				//Update imgy with SIZE
				l_imgy += c_vGridSize[l_y%c_vGridSize.length];
				//Draw Horizontal Line (on the first run of this loop)
				if (l_x == 0 && l_y+1 != l_mapHeight)
				{
					//l_g2d.setColor(c_gridColor);
					//l_g2d.fillRect(0, l_imgy, l_imgWidth, c_vGridSpace[l_y%c_vGridSpace.length]);
					fillRect(l_ret, c_gridColor, 0, l_imgy, l_imgWidth, 
							 			c_vGridSpace[l_y%c_vGridSpace.length]);
				}
				//update imgy with SPACE
				l_imgy += c_vGridSpace[l_y%c_vGridSpace.length];	
			}
			//update imgx with SIZE
			l_imgx += c_hGridSize[l_x%c_hGridSize.length];
			//Draw Vertical Line (we are doing the next column)
			if (l_x+1 != l_mapWidth+1)
			{
				//l_g2d.setColor(c_gridColor);
				//l_g2d.fillRect(l_imgx, 0, c_hGridSpace[l_x%c_hGridSpace.length], l_imgHeight);
				fillRect(l_ret, c_gridColor, l_imgx, 0, 
							c_hGridSpace[l_x%c_hGridSpace.length], l_imgHeight);

			}
			//update imgx with SPACE
			l_imgx += c_hGridSpace[l_x%c_hGridSpace.length];
		}		
		
		return l_ret;
	}
	
	private static void fillRect(BufferedImage p_img, CMYKColor p_color, 
								 int p_x, int p_y, int p_width, int p_height)
	{
		/*if (p_x + p_width > p_img.getWidth() 
				|| p_y + p_height > p_img.getHeight())
		{
			System.err.println("Array index out of bounds on fillrect!");
			return;
		}*/
		
		float[] l_c = { p_color.getCyan(), p_color.getMagenta(), 
						p_color.getYellow(), p_color.getBlack() };
	    float[] l_dbuf = ((DataBufferFloat) 
	    				   p_img.getRaster().getDataBuffer()).getData();
	    int l_doff = 0;	    
	    for (int y = 0; y < p_height; y++)
	    {
	    	//            ROW                   X offset
	    	l_doff = ((y+p_y)*p_img.getWidth() + p_x)*4;
	    	for (int x = 0; x < p_width; x++)
	    	{
		    	System.arraycopy(l_c, 0, l_dbuf, l_doff, 4);
		    	l_doff += 4;
	    	}
	    }	    
	}
	
	/**
	 * Legacy function. Generate an image using the current settings and specified text.
	 * @param p_txt
	 * @return A BufferedImage object with the specified text and padding.
	 */
	public BufferedImage getOldBufferedImage(String p_txt) {
		float l_height, l_width;
		BufferedImage l_ret;
		Graphics2D l_g2d;
		
		//Get the size of the string
		FontRenderContext l_frc = new FontRenderContext(null, false, true);
		l_height = c_txtAscent;
		l_width = (int)c_font.getStringBounds(p_txt, l_frc).getWidth();
		
		//Add padding
		l_height += c_padding*2;
		l_width += c_padding*2;
		
		l_ret = createCMYKImage(Math.round(l_width), Math.round(l_height));
		
		l_g2d = l_ret.createGraphics();
		
		//Draw Background
		l_g2d.setRenderingHint(RenderingHints.KEY_TEXT_ANTIALIASING, 
								RenderingHints.VALUE_TEXT_ANTIALIAS_OFF);
		l_g2d.setColor(new Color(c_defBgColor.getRGB()));
		l_g2d.fillRect(0, 0, (int)l_width, (int)l_height);
		
		//Draw Text
		l_g2d.setFont(c_font);
		l_g2d.setColor(new Color(c_defFontColor.getRGB()));
		l_g2d.drawString(p_txt, c_padding, c_txtAscent+c_padding);
		
		l_ret = GenBlockGrid(l_ret);
		
		return l_ret;
	}	
	
	/**
	 * setCSPRNG - Sets the CSPRNG (if not set by Constructor).
	 * @param p_csprng - the CSPRNG to use.
	 */
	public void setCSPRNG(SecureRandom p_csprng) {
		this.c_csprng = p_csprng;
	}
	
	/**
	 * Sets the current font.
	 * @param p_font - font to use.
	 */
	public void setFont(Font p_font) {
		c_font = p_font;
		c_fontSize = p_font.getSize();
		c_symbolMap = new TreeMap<Character, boolean[][]>();
		generateSymbolMap();
		SetTrueAscent(DEFAULT_SYMBOLS);
	}
	
	public void setGrid(Integer[] p_vGridSize, Integer[] p_vGridSpace, 
						Integer[] p_hGridSize, Integer[] p_hGridSpace)
	{
		//check for 0's and negatives
		for (int l_i = 0; l_i < p_vGridSize.length; l_i++) {
			if (p_vGridSize[l_i] <= 0) p_vGridSize[l_i] = 1;
		}
		for (int l_i = 0; l_i < p_hGridSize.length; l_i++) {
			if (p_hGridSize[l_i] <= 0) p_hGridSize[l_i] = 1;
		}
		for (int l_i = 0; l_i < p_vGridSpace.length; l_i++) {
			if (p_vGridSpace[l_i] < 0) p_vGridSpace[l_i] = 0;
		}
		for (int l_i = 0; l_i < p_hGridSpace.length; l_i++) {
			if (p_hGridSpace[l_i] < 0) p_hGridSpace[l_i] = 0;
		}

		c_vGridSize = p_vGridSize;
		c_hGridSize = p_hGridSize;
		c_vGridSpace = p_vGridSpace;
		c_hGridSpace = p_hGridSpace;		
	}
		
	/**
	 * This function exists because Java doesn't produce a true Ascent value
	 * for any given font. Thus, we do a pixel search to see what the topmost
	 * pixel of the image in the font really is, and subtract that from the
	 * reported ascent. This is pre-computed at instantiation using a given
	 * symbol set.
	 * @param p_txt - The symbol set to be used in the Invisible Ink images.
	 */
	private void SetTrueAscent(String p_txt) {
		float l_height, l_width;
		BufferedImage l_img;
		Graphics2D l_g2d;
		
		//Get the size of the string
		FontRenderContext l_frc = new FontRenderContext(null, false, true);
		l_height = (int)c_font.getLineMetrics(p_txt, l_frc).getAscent();
		l_width = (int)c_font.getStringBounds(p_txt, l_frc).getWidth();
	
		try {
			//Generate image and set colors
			l_img = new BufferedImage((int)l_width, (int)l_height, 
										BufferedImage.TYPE_INT_RGB);
			l_g2d = l_img.createGraphics();
					
			//Draw Text
			l_g2d.setRenderingHint(RenderingHints.KEY_TEXT_ANTIALIASING, 
									RenderingHints.VALUE_TEXT_ANTIALIAS_OFF);
			l_g2d.setFont(c_font);
			l_g2d.setColor(Color.CYAN);	
			l_g2d.drawString(p_txt, 0, l_height); 		
			
			int l_x = 0;
			int l_y = 0;
			int tmp = l_img.getRGB(l_x, l_y);
			//Remember that the image only has 2 colors: background and font
			while (tmp == l_img.getRGB(l_x, l_y)) {
				l_x++;
				if (l_x == l_width) {
					l_y++;
					l_x = 0;
					//If we exceed all bounds, die with default 0.
					if (l_y >= l_height) {
						l_y = 0;
						break;
					}
				}		
			}
			
			c_txtAscent = (int) l_height - l_y;
		} catch(Exception l_e) {
			//If any errors occur, set it to default of "height".
			c_txtAscent = (int) l_height;
		}
	}
	
	private void generateSymbolMap()
	{
		for (int i = 0; i < c_symbols.length(); i++)
		{
			boolean[][] l_map = getMapForSymbol((c_symbols.charAt(i)));
			if (l_map != null)
			{
				c_maxMapWidth = Math.max(l_map.length, c_maxMapWidth);
				if (l_map.length > 0)
				{
					c_maxMapHeight = Math.max(l_map[0].length, c_maxMapHeight);
				}				
			}
		}		
	}
	
	private boolean[][] getMapForSymbol(Character p_symbol)
	{
		if (c_symbolMap.containsKey(p_symbol)) return c_symbolMap.get(p_symbol);
		
		BufferedImage l_img = getSymbolImage(p_symbol);
		int l_ascentStart = l_img.getHeight()-c_txtAscent;
		boolean[][] l_map = new boolean[l_img.getWidth()][l_img.getHeight()-l_ascentStart];
		int l_cyan = Color.CYAN.getRGB();
		for (int l_x = 0; l_x < l_img.getWidth(); l_x++)
		{
			for (int l_y = 0; l_y < l_img.getHeight(); l_y++)
			{
				if (l_y >= l_ascentStart)
				{
					int l_tmp = l_img.getRGB(l_x, l_y);
					if (l_tmp == l_cyan)
					{
						l_map[l_x][l_y - l_ascentStart] = true;
					}
					else
					{
						l_map[l_x][l_y - l_ascentStart] = false;
					}
				}
			}
		}

		c_symbolMap.put(p_symbol, l_map);
		
		return l_map;
	}
	
	private BufferedImage getSymbolImage(Character p_symbol)
	{
		float l_height, l_width;
		BufferedImage l_img;
		Graphics2D l_g2d;
		
		//Get the size of the string
		FontRenderContext l_frc = new FontRenderContext(null, false, true);
		Font l_font =  new Font(c_font.getFontName(), Font.BOLD, c_fontSize);
		l_height = (int)l_font.getLineMetrics(p_symbol.toString(), l_frc).getAscent();
		l_width = (int)l_font.getStringBounds(p_symbol.toString(), l_frc).getWidth();	
		//Generate image and set colors
		l_img = new BufferedImage((int)l_width, (int)l_height, BufferedImage.TYPE_INT_RGB);
		l_g2d = l_img.createGraphics();
		
		//Draw Text
		l_g2d.setRenderingHint(RenderingHints.KEY_TEXT_ANTIALIASING, 
								RenderingHints.VALUE_TEXT_ANTIALIAS_OFF);
		l_g2d.setFont(l_font);
		l_g2d.setColor(Color.CYAN);	
		l_g2d.drawString(p_symbol.toString(), 0, l_height); 				
		
		return l_img;
	}
	
	/**
	 * GenGrid - Generates a grid across a pre-generated image, and sets the 
	 * color inside each grid element to the middle-most pixel. 
	 * @param p_img
	 * @return
	 */
	private BufferedImage GenBlockGrid(BufferedImage p_img) {		
		BufferedImage l_res;
		Graphics2D l_g2d;
		
		//Calculate the width and height of the new image.
		int l_numCols = getTotalCellSize(p_img.getWidth(), c_hGridSize);
		int l_numRows = getTotalCellSize(p_img.getHeight(), c_vGridSize);
		
		//Sample the grid first
		Vector<Vector<Color>> l_gridColors = getGridColors(p_img, 
															l_numCols,
															l_numRows);
		
		//Caclulate the new image size.
		int l_width = 0;
		int l_height = 0;
		for (int l_i = 0; l_i < l_numCols; l_i++)
		{
			l_width += c_hGridSize[l_i%c_hGridSize.length];
			l_width += c_hGridSpace[l_i%c_hGridSize.length];
		}
		for (int l_i = 0; l_i < l_numRows; l_i++)
		{
			l_height += c_vGridSize[l_i%c_vGridSize.length];
			l_height += c_vGridSpace[l_i%c_vGridSize.length];
		}
		
		//Create the grid
		l_res = createCMYKImage(l_width, l_height);
		l_g2d = l_res.createGraphics();
		int l_curx = 0;
		int l_cury = 0;
		for (int l_i = 0; l_i < l_numCols; l_i++)
		{	
			l_cury = 0;
			for (int l_j = 0; l_j < l_numRows; l_j++)
			{
				//Fill in Texel
				l_g2d.setColor(l_gridColors.get(l_i).get(l_j));
				l_g2d.fillRect(l_curx, l_cury, 
								c_hGridSize[l_i%c_hGridSize.length], 
								c_vGridSize[l_i%c_vGridSize.length]);

				l_cury += c_vGridSize[l_i%c_vGridSize.length];
				//Draw Vertical Line (On the first iteration).
				l_cury += c_vGridSpace[l_i%c_vGridSpace.length];
			}
			l_curx += c_hGridSize[l_i%c_hGridSize.length];
			//Draw Horizontal Line
			l_curx += c_hGridSpace[l_i%c_hGridSpace.length];
		}
		
		return l_res;
	}	
	
	/**
	 * Runs through an array of cell sizes, and calculates how many cells need
	 * to be generated.
	 * @param p_size - the size of the image
	 * @param p_cellSizes - the sizes of the cells
	 * @return the number of cells that fit into the image + 1 (round up).
	 */
	private int getTotalCellSize(int p_size, Integer[] p_cellSizes)
	{
		int l_sum = 0;
		int l_index = 0;
		while (l_sum < p_size)
		{
			l_sum += p_cellSizes[l_index%p_cellSizes.length];
			l_index++;
		}
		return l_index;
	}

	/**
	 * Get the color for each texel in the grid.
	 * 
	 * @param p_img
	 * @param p_numCols
	 * @param p_numRows
	 * @return
	 */
	private Vector<Vector<Color>> getGridColors(BufferedImage p_img, 
												int p_numCols, int p_numRows) 
	{
		Vector<Vector<Color>> l_res = new Vector<Vector<Color>>();
		
		int l_x = p_img.getWidth();
		int l_y = p_img.getHeight();
		int l_curx = 0;
		int l_cury = 0;
		int l_cellWidth, l_cellHeight;
		//width left...
		for (int l_i = 0; l_i < p_numCols; l_i++)
		{
			l_res.add(new Vector<Color>());
			l_cellWidth = Math.min(l_x-l_curx, 
									c_hGridSize[l_i%c_hGridSize.length]); 
			//height
			l_cury = 0;
			for (int l_j = 0; l_j < p_numRows; l_j++)
			{
				l_cellHeight = Math.min(l_y-l_cury, 
										c_vGridSize[l_j%c_vGridSize.length]);  
				l_res.get(l_i).add(getGridCellColor(p_img, l_curx, 
						l_cury, l_cellWidth, l_cellHeight));
				l_cury += l_cellHeight;
			}
			l_curx += l_cellWidth;
		}
		return l_res;
	}

	/**
	 * Samples the given cell and returns the foreground or background color
	 * of the texel. This function handles the routines for adding the masking
	 * color and randomizing the texel intensity.
	 * 
	 * @param p_image - the image containing the cell.
	 * @param p_x - the rightmost col of the cell.
	 * @param p_y - the topmost row of the cell.
	 * @param p_sizeX - the width in pixels of the cell.
	 * @param p_sizeY - the height in pixels of the cell.
	 */
	private Color getGridCellColor(BufferedImage p_img, int p_x, int p_y, 
									int p_sizeX, int p_sizeY)
	{
		int l_mCount = 0;	
		Color l_tmp = null;
		float[] tmpFloat = {0,0,0,0};
		//For each pixel, count instance of magenta
		Raster l_tmpRaster = p_img.getRaster();
		
		//System.out.println(p_x + ", " + p_y + ", " + p_sizeX + ", " + p_sizeY);
		/*	
		// Old sampling Method - Deprecated
		for (int l_i = 0; l_i < p_sizeX; l_i++) {
			for (int l_j = 0; l_j < p_sizeY; l_j++) {
				l_tmpRaster.getPixel(l_i+p_x, l_j+p_y, tmpFloat);
				l_tmp = new Color(c_cs, tmpFloat, 1);
				if (l_tmp.equals(c_defFontColor)) l_mCount++;
			}
		}
		*/

		//Simple "Middling" sample method. Sample 9 points, if 5 have magenta
		//make the whole texel magenta
		//Graphics2D l_g2d = p_img.createGraphics();
		int l_i = 0;
		while (l_i < p_sizeX)
		{
			int l_j = 0;
			while (l_j < p_sizeY)
			{
				/* Debugging.
				float l_tmpc[] = {1, 0, 0, 0}; 
				l_g2d.setColor(new Color(c_cs, l_tmpc, 1));
				l_g2d.fillRect(l_i+p_x, l_j+p_y, 1, 1);
				*/
				l_tmpRaster.getPixel(l_i+p_x, l_j+p_y, tmpFloat);
				l_tmp = new Color(c_cs, tmpFloat, 1);
				if (l_tmp.equals(c_defFontColor)) l_mCount++;
				l_j += Math.max(1, Math.round(p_sizeY/4.0));
				
			}
			l_i += Math.max(1, Math.round(p_sizeX/4.0));
		}
		
		//Background Color
		float[] l_color = {0,0,0,0};
		if (l_mCount < 5) {
			l_color = getRandomBgColor();
		}
		else { //Font Color
			l_color = getRandomFontColor();
		}
		l_color = AddMask(l_color);		
		
		return new Color(c_cs, l_color, 1);
	}
	
	private BufferedImage createCMYKImage(int p_width, int p_height)
	{
		//Generate image and set colors
		ComponentColorModel l_ccm = new ComponentColorModel(c_cs, false, false,
													1, DataBuffer.TYPE_FLOAT);
		int[] l_bandoff = {0, 1, 2, 3};
		PixelInterleavedSampleModel l_sm = new PixelInterleavedSampleModel(
												   DataBuffer.TYPE_FLOAT,
												   (int)p_width, (int)p_height, 
										     	   4,(int)p_width*4, l_bandoff);
		WritableRaster l_raster = WritableRaster.createWritableRaster(l_sm, 
																new Point(0,0));
		return new BufferedImage(l_ccm, l_raster, false, null);		
	}
	
	/**
	 * Samples and fills a cell with foreground or background depending on which 
	 * has the most instances of it.
	 * @param p_img - the image containing the cell
	 * @param p_x - the rightmost col of the cell
	 * @param p_y - the top row of the cell
	 * @param p_sizeX - width of cell
	 * @param p_sizeY - length of cell
	 * @return - a modified image
	 *
	private BufferedImage FillGridCell(BufferedImage p_img, int p_x, int p_y, 
									int p_sizeX, int p_sizeY) {
		int l_mCount = 0;	
		Color l_tmp = null;
		float[] tmpFloat = {0,0,0,0};
		//For each pixel, count instance of magenta
		Raster l_tmpRaster = p_img.getRaster();
		for (int l_i = 0; l_i < p_sizeX; l_i++) {
			for (int l_j = 0; l_j < p_sizeY; l_j++) {
				l_tmpRaster.getPixel(l_i+p_x, l_j+p_y, tmpFloat);
				l_tmp = new Color(c_cs, tmpFloat, 1);
				if (l_tmp.equals(c_defFontColor)) l_mCount++;
			}
		}
		Graphics2D l_g2d = p_img.createGraphics();
		//Background Color
		float[] l_color = {0,0,0,0};
		if (l_mCount < p_sizeX*p_sizeY/1.5) {
			l_color = getRandomBgColor();
		}
		else { //Font Color
			l_color = getRandomFontColor();
		}
		l_color = AddMask(l_color);
		l_g2d.setColor(new Color(c_cs, l_color, 1));
		l_g2d.fillRect(p_x, p_y, p_sizeX, p_sizeY);		
		return p_img;
	}*/
	
	/**
	 * AddMask - Uses the preset CSPRNG to generate random additions of
	 * cyan to the image.
	 * @param p_img - image to modify.
	 * @return modified image.
	 */
	private float[] AddMask(float[] p_color) {
		/* TODO: It might be better to have one "addcolor" function, then
		 * just use them differently, instead of 2 that do specific things...
		 */
		if (c_csprng == null) {
			throw new NullPointerException("CSPRNG is not Set!");			
		}
		
		float l_add = c_csprng.nextFloat(); 
		p_color[0] += (c_maxMaskColor[0]-c_minMaskColor[0])*l_add
					+ c_minMaskColor[0];
		p_color[1] += (c_maxMaskColor[1]-c_minMaskColor[1])*l_add
					+ c_minMaskColor[1];
		p_color[2] += (c_maxMaskColor[2]-c_minMaskColor[2])*l_add
					+ c_minMaskColor[2];
		
		return p_color;
	}
	
	private float[] getRandomFontColor() {
		if (c_csprng == null) {
			throw new NullPointerException("CSPRNG is not Set!");			
		}
		float[] l_c = {0,0,0,0};
		float l_s = (float)c_csprng.nextFloat();

		l_c[0] = (c_maxFontColor[0]-c_minFontColor[0])*l_s
					+ c_minFontColor[0];
		l_c[1] = (c_maxFontColor[1]-c_minFontColor[1])*l_s
					+ c_minFontColor[1];
		l_c[2] = (c_maxFontColor[2]-c_minFontColor[2])*l_s
					+ c_minFontColor[2];
		
		return l_c;
	}

	private float[] getRandomBgColor() {
		if (c_csprng == null) {
			throw new NullPointerException("CSPRNG is not Set!");			
		}
		float[] l_c = {0,0,0,0};
		float l_s = (float)c_csprng.nextFloat();

		l_c[0] = (c_maxBgColor[0]-c_minBgColor[0])*l_s
					+ c_minBgColor[0];
		l_c[1] = (c_maxBgColor[1]-c_minBgColor[1])*l_s
					+ c_minBgColor[1];
		l_c[2] = (c_maxBgColor[2]-c_minBgColor[2])*l_s
					+ c_minBgColor[2];							
		return l_c;		
	}
		
	public float[] getMinFontColor() { 
		return c_minFontColor;
	}

	public void setMinFontColor(float[] p_newVal) { 
		c_minFontColor = CMYKColorSpace.normalize(p_newVal);
	}

	
	public float[] getMaxFontColor() {
		return c_maxFontColor;		
	}
	
	public void setMaxFontColor(float[] p_newVal) {
		c_maxFontColor = CMYKColorSpace.normalize(p_newVal);
	}

	public float[] getMinBgColor() {
		return c_minBgColor;		
	}
	
	public void setMinBgColor(float[] p_newVal) {
		c_minBgColor = CMYKColorSpace.normalize(p_newVal);	
	}

	public float[] getMaxBgColor() {
		return c_maxBgColor;		
	}
	
	public void setMaxBgColor(float[] p_newVal) {
		c_maxBgColor = CMYKColorSpace.normalize(p_newVal);
	}

	public float[] getMinMaskColor() {
		return c_minMaskColor;
	}
	
	public void setMinMaskColor(float[] p_newVal) {
		c_minMaskColor = CMYKColorSpace.normalize(p_newVal);
	}
	
	public float[] getMaxMaskColor() {
		return c_maxMaskColor;
	}
	
	public void setMaxMaskColor(float[] p_newVal) {
		c_maxMaskColor = CMYKColorSpace.normalize(p_newVal);		
	}
	
	public int getPadding() {
		return c_padding;
	}
	
	public void setPadding(int p_padding) {
		c_padding = Math.abs(p_padding);
	}

	/**
	 * @param gridColor the gridColor to set
	 */
	public void setGridColor(CMYKColor gridColor) {
		c_gridColor = gridColor;
	}

	/**
	 * @return the gridColor
	 */
	public CMYKColor getGridColor() {
		return c_gridColor;
	}

	/**
	 * @param cache the cache to set
	 */
	public void setCache(boolean cache) {
		c_cache = cache;
		if (isCache())
		{
			c_stringCache = new TreeMap<String, BufferedImage>();
		}
	}

	/**
	 * @return the cache
	 */
	public boolean isCache() {
		return c_cache;
	}

	/**
	 * @return the symbols
	 */
	public String getSymbols() {
		return c_symbols;
	}

	/**
	 * @param p_symbols the symbols to set
	 */
	public void setSymbols(String p_symbols) {
		c_symbols = p_symbols;
		generateSymbolMap();
	}
}
 