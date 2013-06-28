/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.db.TempDataDB.java
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
  *  0.1		15-04-2003	MRo			First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.db;
/**
 * Class containing all the query strings for the TempData
 * 
 * @author MRo
 * 
 */
public class TempDataDB
{
	/**
	 * Private constructor to prevent instantiating
	 * 
	 */
	private TempDataDB()
	{
	}
	public static String SELECT_MAX_ID_TEMP_DATA =
		"SELECT MAX(ID) FROM KOA01.IMPORTTEMP";
	public static String INSERT_TEMP_DATA =
		"INSERT INTO KOA01.IMPORTTEMP (id, type, action, timestamp, importfile) values (?, ?, ?, ?, ?)";
	public static String UPDATE_TEMP_DATA =
		"UPDATE KOA01.IMPORTTEMP set id = ?, timestamp = ?, importfile =? where ";
}
