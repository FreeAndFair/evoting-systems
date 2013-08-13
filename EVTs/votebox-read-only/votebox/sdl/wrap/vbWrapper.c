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

#include "vbWrapper.h"

#define INIT_AUDIO
#define INIT_VIDEO

int vbSDL_Init(int flags)
{
	return SDL_Init(flags);
}

void vbSDL_Quit(void)
{
	SDL_Quit();
}

SDL_Surface* vbSDL_SetVideoMode(int width, int height, int bitsperpixel, int flags)
{
	return SDL_SetVideoMode(width, height, bitsperpixel, flags);
}

SDL_Surface* vbSDL_LoadBMP(char* file_name)
{
	return SDL_LoadBMP(file_name);
}

int vbSDL_SetColors(SDL_Surface* surface, SDL_Color* colors, int firstcolor, int ncolors)
{
	return SDL_SetColors(surface, colors, firstcolor, ncolors);
}

int vbSDL_BlitSurface(SDL_Surface* src, SDL_Rect* srcrect, SDL_Surface* dst, SDL_Rect* dstrect)
{
	return SDL_BlitSurface(src, srcrect, dst, dstrect);
}

void vbSDL_UpdateRect(SDL_Surface* screen, int x, int y, int w, int h)
{
	SDL_UpdateRect(screen, x, y, w, h);
}

void vbSDL_FreeSurface(SDL_Surface* surface)
{
	SDL_FreeSurface(surface);
}

int vbSDL_WaitEvent(SDL_Event *event)
{
	return SDL_WaitEvent(event);
}

void vbSDL_SetClipRect(SDL_Surface *surface, SDL_Rect *rect)
{
	SDL_SetClipRect(surface, rect);
}

int vbSDL_FillRect(SDL_Surface *dst, SDL_Rect *dstrect, int color)
{
	return SDL_FillRect(dst, dstrect, color);
}

void vbSDL_GetClipRect(SDL_Surface *surface, SDL_Rect *rect)
{
	SDL_GetClipRect(surface, rect);
}

SDL_Surface* vbSDL_ConvertSurface(SDL_Surface *src, SDL_PixelFormat *fmt, int flags)
{
	return SDL_ConvertSurface(src, fmt, flags);
}

int Enabled_Elo_Touchscreen(char* device_path)
{
	//We're being... lazy with the buffer.  Probably want to clean this up.
	char* dev_path = malloc(sizeof(char) * 1024);
	
	if(dev_path == NULL)
		return -1;
	
	if(strlen("SDL_MOUSEDEV=") + strlen(device_path) >= 1024)
	{
		free(dev_path);
		return -1;	
	}
	
	if(sprintf(dev_path, "%s=%s", "SDL_MOUSEDEV", device_path) < 0)
	{
		free(dev_path);
		return -1;	
	}
	
    SDL_putenv("SDL_MOUSEDRV=ELO");//We use elo touch screen as mouse
    SDL_putenv(dev_path);//Set the device path to the touchscreen
    
    free(dev_path);	
}

int Event_Get_Type(SDL_Event *event)
{
	return event->type;
}

int Event_Get_Mouse_X(SDL_Event *event)
{
	return event->motion.x;
}

int Event_Get_Mouse_Y(SDL_Event *event)
{
	return event->motion.y;
}

int Event_Get_Mouse_Button(SDL_Event *event)
{
	return event->button.button;
}

int Event_Get_Key(SDL_Event *event)
{
	return event->key.keysym.sym;
}

void Rect_Set(SDL_Rect* rect, int x, int y,int w, int h)
{
	rect->x = x;
	rect->y = y;
	rect->w = w;
	rect->h = h;
}

int Rect_Get_X(SDL_Rect* rect)
{
	return rect->x;
}

int Rect_Get_Y(SDL_Rect* rect)
{
	return rect->y;
}

int Rect_Get_Width(SDL_Rect* rect)
{
	return rect->w;
}

int Rect_Get_Height(SDL_Rect* rect)
{
	return rect->h;
}

SDL_PixelFormat* Surface_Get_Format(SDL_Surface* surface)
{
	return surface->format;
}

Uint32 Surface_Get_Pixel(int x, int y, SDL_Surface* surface)
{
	int unlock = 0;
	
	if(surface == NULL){
		return -1;
	}
		
	if(surface->w <= x || surface->h <= y)
		return -2;
		
	if(x < 0 || y < 0)
		return -3;
		
	if(SDL_MUSTLOCK(surface) != 0){
		if(SDL_LockSurface(surface) != 0)
			return -4;
			
		unlock = 1;
	}//if
	
	//We can only operate on 32-bpp images (rrggbbaa format)
	//Abort if the surface isn't one
	if(surface->format->BitsPerPixel != 32 ||
	   surface->format->Rmask != 0xFF000000 ||
	   surface->format->Gmask != 0x00FF0000 ||
	   surface->format->Bmask != 0x0000FF00 ||
	   surface->format->Amask != 0x000000FF){
			
			if(unlock == 1)
				SDL_UnlockSurface(surface);
			return -5;
	}
	
	int offset = y * surface->pitch/4 + x;
	
	Uint32* pixels = (Uint32*)surface->pixels;
	
	Uint32 val = pixels[offset];
	
	if(unlock == 1)
		SDL_UnlockSurface(surface);
	
	return val;
}

int Surface_Get_Pixel_A(int x, int y, SDL_Surface* surface)
{
	int ret = Surface_Get_Pixel(x, y, surface);
	
	Uint8 r, g, b, a;
	
	SDL_GetRGBA(ret, surface->format, &r, &g, &b, &a);
	
	return ((int)a) & 0xFF;
}

int Surface_Get_Pixel_B(int x, int y, SDL_Surface* surface)
{
	int ret = Surface_Get_Pixel(x, y, surface);
	
	Uint8 r, g, b, a;
	
	SDL_GetRGBA(ret, surface->format, &r, &g, &b, &a);
	
	return ((int)b) & 0xFF;
}

int Surface_Get_Pixel_G(int x, int y, SDL_Surface* surface)
{
	int ret = Surface_Get_Pixel(x, y, surface);
	
	Uint8 r, g, b, a;
	
	SDL_GetRGBA(ret, surface->format, &r, &g, &b, &a);
	
	return ((int)g) & 0xFF;
}

int Surface_Get_Pixel_R(int x, int y, SDL_Surface* surface)
{
	int ret = Surface_Get_Pixel(x, y, surface);
	
	Uint8 r, g, b, a;
	
	SDL_GetRGBA(ret, surface->format, &r, &g, &b, &a);
	
	return ((int)r) & 0xFF;
}

int Surface_Set_Pixel(int x, int y, SDL_Surface* surface, int a, int r, int g, int b)
{
	int unlock = 0;

	if(surface == NULL)
		return -1;
		
	//First, check if the surface needs to be locked
	if(SDL_MUSTLOCK(surface))
		//if yes, try to lock it
		if(SDL_LockSurface(surface) != 0){
			//if that fails, abort
			return -2;
		}else{
			unlock = 1;
		}
			
	//We can only operate on 32-bpp images (rrggbbaa format)
	//Abort if the surface isn't one
	if(surface->format->BitsPerPixel != 32 ||
	   surface->format->Rmask != 0xFF000000 ||
	   surface->format->Gmask != 0x00FF0000 ||
	   surface->format->Bmask != 0x0000FF00 ||
	   surface->format->Amask != 0x000000FF){
			
			if(unlock == 1)
				SDL_UnlockSurface(surface);
			return -3;
	}
	
	Uint32* pixels = (Uint32*)surface->pixels;
	
	Uint32 pixelValue = SDL_MapRGBA(surface->format, r, g, b, a);
	int offset = (surface->pitch/4 * y) + x;
	
	pixels[offset] = pixelValue;
	
	if(unlock == 1)
		SDL_UnlockSurface(surface);
	
	return 0;
}

SDL_Surface* Alloc_Surface(int width, int height)
{
	//Alloc a surface of width x height, with 32 bpp, in RGBA format
	//Putting it in RAM rather than VMEM so we can guarantee the format request is honored
	return SDL_CreateRGBSurface(SDL_SWSURFACE, width, height, 32,
								0xFF000000, 0x00FF0000, 0x0000FF00, 0x000000FF);
}

SDL_Event* Alloc_Event()
{
	return (SDL_Event*)malloc(sizeof(SDL_Event));
}

void Free_Event(SDL_Event* event)
{
	free(event);
}

SDL_Rect* Alloc_Rect()
{
	return (SDL_Rect*)malloc(sizeof(SDL_Rect));
}

void Free_Rect(SDL_Rect* rect)
{
	free(rect);
}
