/*
 * @(#)SysBeep.java.java
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

import java.awt.Toolkit;
import java.util.Timer;
import java.util.TimerTask;

/**
 * @author John Conway
 *
 */
public class SysBeep implements Runnable
{
	private int c_count = 0;
	private long c_delay = 0;
	private Timer c_timer;
	
	public SysBeep(int p_count, long p_delay)
	{
		c_count = p_count; 
		c_delay = p_delay;
		
		c_timer = new Timer();
	}
	
	/* (non-Javadoc)
	 * @see java.lang.Runnable#run()
	 */
	public void run()
	{
		for(int i = 0; i < c_count; i++)
		{
			Toolkit.getDefaultToolkit().beep();
			try
			{
				Thread.sleep(200);
			}
			catch (InterruptedException e)
			{
				// TODO Auto-generated catch block
				//e.printStackTrace();
			}
		}
	}
}
