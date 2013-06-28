/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.databeheer.dataobjects.ExportItem.java
  *
  * -----------------------------------------------------------------------
  * 
  *  (c) 2003  Ministerie van Binnenlandse Zaken en Koninkrijkrelaties
  *
  *  Project		: Kiezen Op Afstand (KOA)
  *  Project Number	: ECF-2651
  *  
  *  History:
  *  Version	Date		Name		Reason
  * ---------------------------------------------------------
  *  0.1		28-04-2003	MRo			First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.databeheer.dataobjects;
import java.util.Date;
/**
 * Class representing a export item for the data manager.
 * 
 * @author RMo
 * 
 */
public class ExportItem implements java.io.Serializable
{
	private int id;
	private String type;
	private Date date;
	/**
	 * Constructor for the exportitem
	 * 
	 * @param id The ID of the export item
	 * @param type The type of the export item
	 * @param date Date representation
	 * 
	 */
	public ExportItem(int id, String type, Date date)
	{
		this.id = id;
		this.type = type;
		this.date = date;
	}
	/**
	 * Gets the id
	 * @return Returns a int
	 */
	public int getId()
	{
		return id;
	}
	/**
	 * Sets the id
	 * @param id The id to set
	 */
	public void setId(int id)
	{
		this.id = id;
	}
	/**
	 * Gets the type
	 * @return Returns a String
	 */
	public String getType()
	{
		return type;
	}
	/**
	 * Sets the type
	 * @param type The type to set
	 */
	public void setType(String type)
	{
		this.type = type;
	}
	/**
	 * Gets the date
	 * @return Returns a Date
	 */
	public Date getDate()
	{
		return date;
	}
	/**
	 * Sets the date
	 * @param date The date to set
	 */
	public void setDate(Date date)
	{
		this.date = date;
	}
}