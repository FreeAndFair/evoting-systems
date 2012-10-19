/*
 * @(#)Candidate.java.java
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

/**
 * 
 * @author Richard Carback
 *
 */
public class Contestant implements Comparable
{
	protected String c_name = null;
	protected Integer c_id = -1;
	protected ContestantType c_state = ContestantType.ORIGINAL;
	
	public enum ContestantType
	{
		ORIGINAL,
		WRITEIN,
		RESOLVED
	};
	
	/** 
	 * Creates a bad contestant.
	 */
	public Contestant()
	{
		super();
		c_name = "No Name";
		c_id = -1;
	}
	
	public Contestant(int p_id, String p_name, ContestantType p_state)
	{
		super();
		c_state = p_state;
		c_id = p_id;
		c_name = p_name;
	}
	
	/**
	 * @param p_id
	 * @param p_name
	 */
	public Contestant(int p_id, String p_name)
	{
		super();
		c_name = p_name;
		c_id = p_id;
	}
	/**
	 * @return the name
	 */
	public String getName()
	{
		return c_name;
	}
	/**
	 * @param p_name the name to set
	 */
	public void setName(String p_name)
	{
		c_name = p_name;
	}
	/**
	 * @return the id
	 */
	public Integer getId()
	{
		return c_id;
	}
	/**
	 * @param p_id the id to set
	 */
	public void setId(Integer p_id)
	{
		c_id = p_id;
	}
	
	/* (non-Javadoc)
	 * @see java.lang.Object#hashCode()
	 */
	@Override
	public int hashCode()
	{
		final int prime = 31;
		int result = 1;
		result = prime * result + c_id;
		result = prime * result + ((c_name == null) ? 0 : c_name.hashCode());
		return result;
	}
	
	/* (non-Javadoc)
	 * @see java.lang.Object#equals(java.lang.Object)
	 */
	@Override
	public boolean equals(Object obj)
	{
		if (this == obj)
			return true;
		if (obj == null)
			return false;

		if (c_id.getClass() == obj.getClass())
			return c_id.equals(obj);

		
		if (getClass() != obj.getClass())
			return false;
		Contestant other = (Contestant) obj;
		if (c_id != other.c_id)
			return false;
		if (c_name == null)
		{
			if (other.c_name != null)
				return false;
		}
		else if (!c_name.equals(other.c_name))
			return false;
		return true;
	}		
	
	public String toString()
	{
		return new String(c_name + "(" + c_id + ")");
	}
	

	public ContestantType getCandidateType()
	{
		return c_state;
	}
	
	/* (non-Javadoc)
	 * @see java.lang.Comparable#compareTo(java.lang.Object)
	 */
	public int compareTo(Object p_o)
	{	
		if (c_id.getClass() == p_o.getClass())
			return c_id.compareTo((Integer)p_o);
		else if (getClass() == p_o.getClass())
			return c_id.compareTo(((Contestant)p_o).getId());
		else return 0; //Equals if we don't know what it is..
	}
}
