/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.dataobjects.Kieskring.java
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
  *  0.1		13-05-2003	AGr			First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.dataobjects;
import java.io.Serializable;
/**
 * Dataobject that contains data about a kieskring
 */
public class Kieskring implements java.io.Serializable
{
	private String sKieskringNaam;
	private String sKieskringnummer;
	public String getKieskringNaam()
	{
		return sKieskringNaam;
	}
	public void setKieskringNaam(String sNewKieskringNaam)
	{
		sKieskringNaam = sNewKieskringNaam;
	}
	public String getKieskringnummer()
	{
		return sKieskringnummer;
	}
	public void setKieskringnummer(String sNewKieskringNummer)
	{
		sKieskringnummer = sNewKieskringNummer;
	}
}
