/*
 * @(#)JudgeAuthentication.java.java
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
package org.scantegrity.scanner.deprecated;

import java.math.BigInteger;

import org.scantegrity.scanner.ScannerConfig;

/**
 * @author John Conway
 *
 */
public class JudgeAuthentication
{	
	public static boolean authorizeJudge(BigInteger p_hashPin, ScannerConfig p_config)
	{
		final BigInteger l_b = new BigInteger(p_config.getJudgePassHash().get(0)) ;
		
		System.out.println("Config Hash:" + l_b);
		
		if(l_b.equals(p_hashPin))
			return false; 
		
		return true;
	}
}
