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

package votebox;

import java.awt.image.BufferedImage;
import java.awt.image.PixelGrabber;
import java.util.Observable;
import java.util.Observer;

import votebox.middle.view.VoteboxSDLViewFactory;
import votebox.sdl.*;

import javax.imageio.*;

import auditorium.IAuditoriumParams;

import java.io.*;

public class VoteBoxSDLInactiveUI implements Runnable, IVoteBoxInactiveUI{

	static{
		System.loadLibrary("SDL_wrap");
	}
	
	private VoteBox _votebox = null;
	private IAuditoriumParams _config = null;
	private SWIGTYPE_p_SDL_Surface _video;
	
	private SWIGTYPE_p_SDL_Surface[] _numbers;
	private SWIGTYPE_p_SDL_Rect[] _numberSizes;
	private SWIGTYPE_p_SDL_Rect[] _numberLocations;
	
	private SWIGTYPE_p_SDL_Rect _titleSize;
	private SWIGTYPE_p_SDL_Rect _waitingSize;
	
	private SWIGTYPE_p_SDL_Surface _titleLbl;
	private SWIGTYPE_p_SDL_Surface _waitingLbl;
	
	
	private Thread _killThread = null;
	private boolean _kill = false;
	
	public VoteBoxSDLInactiveUI(VoteBox vb, IAuditoriumParams config){
		_votebox = vb;
		_config = config;
		
		try {
			init();
		} catch (FileNotFoundException e) {
			System.out.println("Failed to init VoteBoxSDLInactiveUI");
			e.printStackTrace(System.err);
			System.exit(-1);
		} catch (IOException e) {
			System.out.println("Failed to init VoteBoxSDLInactiveUI");
			e.printStackTrace(System.err);
			System.exit(-1);
		} catch (InterruptedException e) {
			System.out.println("Failed to init VoteBoxSDLInactiveUI");
			e.printStackTrace(System.err);
			System.exit(-1);
		}
		
		_votebox.registerForLabelChanged(new Observer(){
    		public void update(Observable o, Object arg){
    			try{
    				drawNumbers();
    			}catch(Exception e){
    				throw new RuntimeException(e);
    			}
    		}//update
    	});
    }
	
	public void run(){
		SWIGTYPE_p_SDL_Event event = SDL.Alloc_Event();
		
		while(!_kill){
			try{
				//Ignore erroneous events
				if(SDL.vbSDL_WaitEvent(event) == 0) continue;
				
				if(SDL.Event_Get_Type(event) == SDLEnum.KEYUP_TYPE){
					
					if(SDL.Event_Get_Key(event) == 120){
						
						_kill = true;
						disable(false);
						SDL.Free_Event(event);
						SDL.vbSDL_Quit();
						System.exit(0);
					}//if
				}//if
			}catch(Exception e){
				e.printStackTrace();
			}//catch
		}//while
		
		SDL.Free_Event(event);
	}//run
	
	private void disable() throws Exception{
		disable(true);
	}
	
	private void disable(boolean doJoin) throws Exception{
		_kill = true;
		
		if(doJoin && _killThread != null)
			_killThread.join(1000);
		
		_killThread = null;
	}//disable
	
	private void init() throws FileNotFoundException, IOException, InterruptedException{
		votebox.middle.view.VoteboxSDLViewFactory.initSDL(_config);
		
		_video = VoteboxSDLViewFactory.MAIN_VIDEO;
		_titleSize = SDL.Alloc_Rect();
    	_titleLbl = loadTitleImage(_titleSize);
    	
    	_numbers = new SWIGTYPE_p_SDL_Surface[10];
    	_numberSizes = new SWIGTYPE_p_SDL_Rect[10];
    	for(int i = 0; i <= 9; i++){
    		String filename = "";
    		switch(i){
    		case 0 : filename = "zero.png"; break;
    		case 1 : filename = "one.png"; break;
    		case 2 : filename = "two.png"; break;
    		case 3 : filename = "three.png"; break;
    		case 4 : filename = "four.png"; break;
    		case 5 : filename = "five.png"; break;
    		case 6 : filename = "six.png"; break;
    		case 7 : filename = "seven.png"; break;
    		case 8 : filename = "eight.png"; break;
    		case 9 : filename = "nine.png"; break;
    		default: throw new RuntimeException("Invalid number count");
    		}//switch
    		
    		_numberSizes[i] = SDL.Alloc_Rect();
    		_numbers[i] = loadImage(getInputStream(filename), _numberSizes[i]);
    	}//for
    	
    	_numberLocations = new SWIGTYPE_p_SDL_Rect[8];
    	for(int i = 0; i < 8; i++){
    		_numberLocations[i] = SDL.Alloc_Rect();
    		SDL.Rect_Set(_numberLocations[i], i * 128, 768/2 - 20, 128, 40);
    	}//for
    	
    	_waitingSize = SDL.Alloc_Rect();
    	_waitingLbl = loadWaitingImage(_waitingSize);
	}//init
	
	private void enable() throws Exception{
    	SWIGTYPE_p_SDL_Rect dstrect = SDL.Alloc_Rect();
		SDL.Rect_Set(dstrect, 0, 0, 1024, 768);
		
		SDL.vbSDL_FillRect(_video, dstrect, 0xFFFFFFFF);
		
		SDL.Free_Rect(dstrect);
    	
    	int xOffset = 1024/2 - SDL.Rect_Get_Width(_titleSize)/2;
    	int yOffset = 20;
    	
    	dstrect = SDL.Alloc_Rect();
    	SDL.Rect_Set(dstrect, xOffset, yOffset, SDL.Rect_Get_Width(_titleSize), SDL.Rect_Get_Height(_titleSize));
    	
    	SDL.vbSDL_BlitSurface(_titleLbl, _titleSize, _video, dstrect);
    	SDL.Free_Rect(dstrect);
    	
    	drawNumbers();
    	
    	xOffset = 1024/2 - SDL.Rect_Get_Width(_waitingSize)/2;
    	yOffset = 20;
    	
    	dstrect = SDL.Alloc_Rect();
    	SDL.Rect_Set(dstrect, xOffset, 768 - yOffset - SDL.Rect_Get_Height(_waitingSize), SDL.Rect_Get_Width(_waitingSize), SDL.Rect_Get_Height(_waitingSize));
    	
    	SDL.vbSDL_BlitSurface(_waitingLbl, _waitingSize, _video, dstrect);
    	SDL.Free_Rect(dstrect);
    	
    	SDL.vbSDL_UpdateRect(_video, 0, 0, 0, 0);
    	
    	_kill = false;
    	_killThread = new Thread(this);
    	_killThread.start();
	}
	
	public synchronized void setVisible(boolean b){		
		try{
			if(b)
				enable();
			else
				disable();
			
			SDL.vbSDL_UpdateRect(_video, 0, 0, 0, 0);
		}catch(Exception e){
			throw new RuntimeException(e);
		}
	}//setVisible
	
	private void drawNumbers(){
		String labelStr = null;
		if(_votebox.getLabel() == 0){
			//labelStr = "12345";
			return;
		}else{
			labelStr = ""+_votebox.getLabel();
		}
		
		char[] chars = labelStr.toCharArray();
		
		for(int j = chars.length - 1; j>= 0; j--){
			int loc = j + (_numberLocations.length - chars.length);
			
			SWIGTYPE_p_SDL_Surface img = null;
			SWIGTYPE_p_SDL_Rect srcrect = null;
			
			switch(chars[j])
			{
			case '0': img = _numbers[0]; srcrect = _numberSizes[0]; break;
			case '1': img = _numbers[1]; srcrect = _numberSizes[1]; break;
			case '2': img = _numbers[2]; srcrect = _numberSizes[2]; break;
			case '3': img = _numbers[3]; srcrect = _numberSizes[3]; break;
			case '4': img = _numbers[4]; srcrect = _numberSizes[4]; break;
			case '5': img = _numbers[5]; srcrect = _numberSizes[5]; break;
			case '6': img = _numbers[6]; srcrect = _numberSizes[6]; break;
			case '7': img = _numbers[7]; srcrect = _numberSizes[7]; break;
			case '8': img = _numbers[8]; srcrect = _numberSizes[8]; break;
			case '9': img = _numbers[9]; srcrect = _numberSizes[9]; break;
			default: throw new RuntimeException("Invalid character in label string");
			}
			
			SWIGTYPE_p_SDL_Rect dstrect = _numberLocations[loc];
			SDL.vbSDL_BlitSurface(img, srcrect, _video, dstrect);
		}//for
		
		SDL.vbSDL_UpdateRect(_video, 0, 0, 0, 0);
	}//drawNumbers
	
	private SWIGTYPE_p_SDL_Surface loadImage(InputStream in, SWIGTYPE_p_SDL_Rect size) throws IOException, InterruptedException{
		BufferedImage bi = ImageIO.read(in);

		if(size != null)
			SDL.Rect_Set(size, 0, 0, bi.getWidth(), bi.getHeight());

		SWIGTYPE_p_SDL_Surface surface = SDL.Alloc_Surface(bi.getWidth(), bi.getHeight());
		
		int width = bi.getWidth();
		int height = bi.getHeight();
		
		int[] pixels = new int[width * height];
		PixelGrabber grabber = new PixelGrabber(bi, 0, 0, width, height, pixels, 0, width);
		
		//Grab all the pixels in aarrggbb format
		boolean success = grabber.grabPixels();
		
		if(!success)
			throw new RuntimeException("VoteboxSDLImage grabPixels failed!");
		
		//Pass these pixels across to SDL one-by-one
		for(int y = 0; y < height; y++)
			for(int x = 0; x < width; x++){
				int pixel = pixels[y * width + x];
				int a = (pixel >> 24) & 0xFF;
				int r = (pixel >> 16) & 0xFF;
				int g = (pixel >>  8) & 0xFF;
				int b = (pixel >>  0) & 0xFF;
				
				int result = SDL.Surface_Set_Pixel(x, y, surface, a, r, g, b);
				
				if(result == -1)
					throw new RuntimeException("Error occurred while setting pixel on surface");
			}//for
		
		//Make sure that the changes stick to the surface before anyone tries to blit with it
		SDL.vbSDL_UpdateRect(surface, 0, 0, width, height);
		
		return surface;
	}//loadImage
	
	private InputStream getInputStream(String resourceName) throws FileNotFoundException{
		InputStream in = this.getClass().getClassLoader().getResourceAsStream("images/"+resourceName);
		
		if(in != null) return in;
		
		return new FileInputStream(new File(new File("images"), resourceName));
	}//getInputStream
	
	private SWIGTYPE_p_SDL_Surface loadWaitingImage(SWIGTYPE_p_SDL_Rect size) throws FileNotFoundException, IOException, InterruptedException{
		return loadImage(getInputStream("waiting.png"), size);
	}//loadWaitingImage
	
	private SWIGTYPE_p_SDL_Surface loadTitleImage(SWIGTYPE_p_SDL_Rect size) throws FileNotFoundException, IOException, InterruptedException{
		return loadImage(getInputStream("title.png"), size);
	}//loadTitleImage
}
