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

import java.awt.Rectangle;
import java.util.HashSet;

import votebox.sdl.*;

/**
 * New SDL View implementation.
 * 
 * Draws to the global surface held in VoteboxSDLViewFactory.
 * @author Montrose
 */
public class VoteboxSDLView extends AView {

	//*** Key Bindings ***
    public static final int CAST_BALLOT_BUTTON = 99;//SDLKey.SDLK_c;
    public static final int NEXT_PAGE_BUTTON = 46;//SDLKey.SDLK_PERIOD;
    public static final int PREV_PAGE_BUTTON = 44;//SDLKey.SDLK_COMMA;
    public static final int SELECT_BUTTON = 13;//SDLKey.SDLK_RETURN;
    public static final int LEFT_BUTTON = 276;//SDLKey.SDLK_LEFT;
    public static final int RIGHT_BUTTON = 275;//SDLKey.SDLK_RIGHT;
    public static final int UP_BUTTON = 273;//SDLKey.SDLK_UP;
    public static final int DOWN_BUTTON = 274;//SDLKey.SDLK_DOWN;
    public static final int NEXT_BUTTON = 110;//SDLKey.SDLK_n;
    public static final int PREVIOUS_BUTTON = 112;//SDLKey.SDLK_p;
    public static final int KILL_BUTTON = 120;//SDLKey.SDLK_x;

    // *** Fields ***
    private votebox.sdl.SWIGTYPE_p_SDL_Surface _video = VoteboxSDLViewFactory.MAIN_VIDEO;
    private SWIGTYPE_p_SDL_Rect _bounds;
    private boolean _running;

    /**
     * Construct an SDLView
     */
    public VoteboxSDLView() {
        super();
        _running = false;
    }

    /**
     * @see votebox.middle.view.IView#clearDisplay()
     */
    public void clearDisplay() {
        if (!_running)
            return;

        SDL.vbSDL_SetClipRect(_video, _bounds);
        SDL.vbSDL_FillRect(_video, _bounds, 0xFFFFFFFF);

        //Update the whole of _video
        SDL.vbSDL_UpdateRect(_video, 0, 0, 0, 0);

        _currentDrawables.clear();
        _hitboxMap.clear();
    }

    /**
     * @see votebox.middle.view.IView#dispose()
     */
    public void dispose() {
    	clearDisplay();
        _running = false;
        SDL.Free_Rect(_bounds);
        ((VoteboxSDLImage)_background.getImage()).release();
    }

    /**
     * @see votebox.middle.view.IView#invalidate(votebox.middle.view.IDrawable)
     */
    public void invalidate(IDrawable drawable) {
        if (!_running)
            return;
        
        deliver(EventType.BEGIN_PAGE_REDRAW, InputEvent.NONE);

        //Set a clip so we only draw on the relevant parts of _video
        SWIGTYPE_p_SDL_Rect cliprect =  SDL.Alloc_Rect();
        SDL.Rect_Set(cliprect, drawable.getX(), drawable.getY(), drawable.getImage().getWidth(), drawable.getImage().getHeight());
        SDL.vbSDL_SetClipRect(_video, cliprect);
        SDL.Free_Rect(cliprect);

        Rectangle jCliprect = new Rectangle(drawable.getX(), drawable.getY(), drawable.getImage().getWidth(), drawable.getImage().getHeight());

        HashSet<IDrawable> redrawset = new HashSet<IDrawable>();
        for (IDrawable d : _currentDrawables)
        	if (jCliprect.contains( _hitboxMap.get( d ) ))
        		redrawset.add( d );

        if (_background != null){
        	//Blit background to the screen.
        	//Note that we do not free it, as its conversion is quite costly in comparison to other images
        	SWIGTYPE_p_SDL_Rect blitRect = SDL.Alloc_Rect();
        	SWIGTYPE_p_SDL_Rect srcRect = SDL.Alloc_Rect();
        	SDL.Rect_Set(blitRect, _background.getX(), _background.getY(), _background.getImage().getWidth(), _background.getImage().getHeight());
        	SDL.Rect_Set(srcRect, 0, 0, _background.getImage().getWidth(), _background.getImage().getHeight());

        	SWIGTYPE_p_SDL_Surface backImg = (SWIGTYPE_p_SDL_Surface)((VoteboxSDLImage)_background.getImage()).getImage();

        	SDL.vbSDL_BlitSurface(backImg, srcRect, _video, blitRect);

        	SDL.Free_Rect(blitRect);
        	SDL.Free_Rect(srcRect);
        }//if

        for (IDrawable id : _currentDrawables)
        	if (redrawset.contains( id )){
        		//Blit id to the screen
        		SWIGTYPE_p_SDL_Rect redrawRect = SDL.Alloc_Rect();
        		SDL.Rect_Set(redrawRect, id.getX(), id.getY(), id.getImage().getWidth(), id.getImage().getHeight());
        		SWIGTYPE_p_SDL_Rect redrawSrc = SDL.Alloc_Rect();
        		SDL.Rect_Set(redrawSrc, 0, 0, id.getImage().getWidth(), id.getImage().getHeight());
        		SWIGTYPE_p_SDL_Surface redrawSurface = (SWIGTYPE_p_SDL_Surface)((VoteboxSDLImage)id.getImage()).getImage();

        		SDL.vbSDL_BlitSurface(redrawSurface, redrawSrc, _video, redrawRect);

        		SDL.Free_Rect(redrawRect);
        		SDL.Free_Rect(redrawSrc);

        		//Go ahead and release this image, as we can't be 100% that we'll be given the opportunity to
        		//do so again
        		((VoteboxSDLImage)id.getImage()).release();
        	}//if

        //Update all of _video
        SDL.vbSDL_UpdateRect(_video, 0, 0, 0, 0);
        
        deliver(EventType.END_PAGE_REDRAW, InputEvent.NONE);
    }
    
    /**
     * @see votebox.middle.view.IView#run(java.lang.Runnable)
     */
    public void run(final Runnable lambda) {
        new Thread( new Runnable() {

            public void run() {
            	_bounds = SDL.Alloc_Rect();
            	SDL.vbSDL_GetClipRect(_video, _bounds);
            	_running = true;

            	lambda.run();

            	for(IDrawable d : _currentDrawables)
            		invalidate(d);

            	SWIGTYPE_p_SDL_Event event = SDL.Alloc_Event();

            	while(_running){
            		SDL.vbSDL_WaitEvent(event);

            		serviceEvent(event);
            	}//while

            	SDL.Free_Event(event);
            }

        } ).start();
    }
    
    /**
     * Given an SDL event that has been noticed, execute the correct handler (if
     * one has been registered).
     * 
     * @param event
     *            This is the event noticed.
     */
    private void serviceEvent(SWIGTYPE_p_SDL_Event event){
        // deliver it to the event manager
    
    	if(SDL.Event_Get_Type(event) == SDLEnum.KEYUP_TYPE){
    		int keycode = SDL.Event_Get_Key(event);
    		
    		switch(keycode){
    			case CAST_BALLOT_BUTTON: deliver( EventType.CAST_BALLOT, InputEvent.NONE); break;
    			case NEXT_PAGE_BUTTON: deliver( EventType.NEXT_PAGE, InputEvent.NONE); break;
    			case PREV_PAGE_BUTTON: deliver( EventType.PREV_PAGE, InputEvent.NONE); break;
    			case SELECT_BUTTON: deliver( EventType.SELECT, InputEvent.NONE); break;
    			case LEFT_BUTTON: deliver( EventType.LEFT, InputEvent.NONE); break;
    			case RIGHT_BUTTON: deliver( EventType.RIGHT, InputEvent.NONE); break;
    			case UP_BUTTON: deliver( EventType.UP, InputEvent.NONE); break;
    			case DOWN_BUTTON: deliver( EventType.DOWN, InputEvent.NONE); break;
    			case NEXT_BUTTON: deliver( EventType.NEXT, InputEvent.NONE); break;
    			case PREVIOUS_BUTTON: deliver( EventType.PREVIOUS, InputEvent.NONE); break;
    			case KILL_BUTTON: deliver( EventType.KILL, InputEvent.NONE); break;
    		}//switch
    		
    		return;
    	}
    	
    	if(SDL.Event_Get_Type(event) == SDLEnum.MOUSE_DOWN_TYPE){
    		int x = SDL.Event_Get_Mouse_X(event);
    		int y = SDL.Event_Get_Mouse_Y(event);
    		
    		deliver( EventType.MOUSE_DOWN, new InputEvent(
                    getFocusableFromHitbox(x, y)));
    		
    		return;
    	}
    	
    	if(SDL.Event_Get_Type(event) == SDLEnum.MOUSE_MOTION_TYPE){
    		int x = SDL.Event_Get_Mouse_X(event);
    		int y = SDL.Event_Get_Mouse_Y(event);
    		
    		deliver( EventType.MOUSE_MOVE, new InputEvent(
                    getFocusableFromHitbox(x, y)));
    		
    		return;
    	}
    }

}