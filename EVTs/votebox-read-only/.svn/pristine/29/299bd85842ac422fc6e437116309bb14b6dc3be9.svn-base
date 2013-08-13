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

import auditorium.IAuditoriumParams;
import votebox.sdl.SDL;
import votebox.sdl.SDLEnum;
import votebox.sdl.SWIGTYPE_p_SDL_Surface;

/**
 * The new SDL View Factory.
 * Creates SDL views for Votebox based on our custom SDL wrapper.
 * 
 * Shares a constant full screen SDL_Surface for drawing between all
 * instance of the Inactive and Active UI.
 * 
 * @author Montrose
 *
 */
public class VoteboxSDLViewFactory implements IViewFactory {
	public static SWIGTYPE_p_SDL_Surface MAIN_VIDEO = null;
	
	private static boolean NEEDS_INIT = true;
	
	private IAuditoriumParams _config = null;
	
	/**
	 * Construct a new factory.
	 * 
	 * @param config - configuration information for whether or not to attempt to use an Elo touch screen.
	 */
	public VoteboxSDLViewFactory(IAuditoriumParams config){
		_config = config;
	}//VoteboxSDLViewFactory
	
	/**
	 * When first called, will create a global full screen display and - if necissary - try to connect
	 * to an attached touchscreen.
	 * 
	 * @param config - configuration info. for the touch screen.
	 */
	public static void initSDL(IAuditoriumParams config){
		if(NEEDS_INIT){
			//Link in our lib*.so or *.dll as an SDL bridge
			System.loadLibrary("SDL_wrap");
			
			if(config.getUseEloTouchScreen())
				SDL.Enabled_Elo_Touchscreen(config.getEloTouchScreenDevice());
			
        	//We initialize video, requesting a hardware surface and fullscreen mode
        	SDL.vbSDL_Init(SDLEnum.INIT_VIDEO);
        	
        	MAIN_VIDEO = SDL.vbSDL_SetVideoMode(1024, 768, 0, SDLEnum.HWSURFACE | SDLEnum.FULLSCREEN);
        	
        	if(MAIN_VIDEO == null){
        		SDL.vbSDL_Quit();
        		
        		throw new RuntimeException("Unable to allocate SDL MAIN_VIDEO");
        	}//if
        	
        	NEEDS_INIT = false;
		}//if
	}//initSDL
	
	/**
	 * Creates a displayable image out of a file.
	 * 
	 * @param path - File to load/wrap.
	 */
	public IViewImage makeImage(String path) {
		return new VoteboxSDLImage(path);
	}

	/**
	 * Creates a new VoteboxSDLView.
	 * 
	 * @return a new View.
	 */
	public IView makeView() {
		initSDL(_config);
		
		return new VoteboxSDLView();
	}

}
