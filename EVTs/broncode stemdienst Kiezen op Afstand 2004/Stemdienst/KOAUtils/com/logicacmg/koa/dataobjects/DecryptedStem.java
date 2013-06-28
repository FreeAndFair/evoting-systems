/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.dataobjects.DecryptedStem.java
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
  *  0.1.8		20-07-2003	XUi			First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.dataobjects;
public class DecryptedStem implements java.io.Serializable
{
	String sKandidaatCode = null;
	String sKieskringnummer = null;
	String sDistrictnummer = null;
	String sKieslijstnummer = null;
	String sPositienummer = null;
	String sLijstnaam = null;
	String sAchternaam = null;
	String sVoorletters = null;
	public DecryptedStem(
		String kandidaatcode,
		String kieskringnummer,
		String districtnummer,
		String kieslijstnummer,
		String positienummer,
		String lijstnaam,
		String achternaam,
		String voorletters)
	{
		sKandidaatCode = kandidaatcode;
		sKieskringnummer = kieskringnummer;
		sDistrictnummer = districtnummer;
		sKieslijstnummer = kieslijstnummer;
		sPositienummer = positienummer;
		sLijstnaam = lijstnaam;
		sAchternaam = achternaam;
		sVoorletters = voorletters;
	}
	public DecryptedStem()
	{
	}
	/**
	 * Gets the achternaam
	 * @return Returns a String
	 */
	public String getAchternaam()
	{
		return sAchternaam;
	}
	/**
	 * Sets the achternaam
	 * @param achternaam The achternaam to set
	 */
	public void setAchternaam(String achternaam)
	{
		sAchternaam = achternaam;
	}
	/**
	 * Gets the districtnummer
	 * @return Returns a String
	 */
	public String getDistrictnummer()
	{
		return sDistrictnummer;
	}
	/**
	 * Sets the districtnummer
	 * @param districtnummer The districtnummer to set
	 */
	public void setDistrictnummer(String districtnummer)
	{
		sDistrictnummer = districtnummer;
	}
	/**
	 * Gets the kandidaatCode
	 * @return Returns a String
	 */
	public String getKandidaatCode()
	{
		return sKandidaatCode;
	}
	/**
	 * Sets the kandidaatCode
	 * @param kandidaatCode The kandidaatCode to set
	 */
	public void setKandidaatCode(String kandidaatCode)
	{
		sKandidaatCode = kandidaatCode;
	}
	/**
	 * Gets the kieskringnummer
	 * @return Returns a String
	 */
	public String getKieskringnummer()
	{
		return sKieskringnummer;
	}
	/**
	 * Sets the kieskringnummer
	 * @param kieskringnummer The kieskringnummer to set
	 */
	public void setKieskringnummer(String kieskringnummer)
	{
		sKieskringnummer = kieskringnummer;
	}
	/**
	 * Gets the kieslijstnummer
	 * @return Returns a String
	 */
	public String getKieslijstnummer()
	{
		return sKieslijstnummer;
	}
	/**
	 * Sets the kieslijstnummer
	 * @param kieslijstnummer The kieslijstnummer to set
	 */
	public void setKieslijstnummer(String kieslijstnummer)
	{
		sKieslijstnummer = kieslijstnummer;
	}
	/**
	 * Gets the lijstnaam
	 * @return Returns a String
	 */
	public String getLijstnaam()
	{
		return sLijstnaam;
	}
	/**
	 * Sets the lijstnaam
	 * @param lijstnaam The lijstnaam to set
	 */
	public void setLijstnaam(String lijstnaam)
	{
		sLijstnaam = lijstnaam;
	}
	/**
	 * Gets the positienummer
	 * @return Returns a String
	 */
	public String getPositienummer()
	{
		return sPositienummer;
	}
	/**
	 * Sets the positienummer
	 * @param positienummer The positienummer to set
	 */
	public void setPositienummer(String positienummer)
	{
		sPositienummer = positienummer;
	}
	/**
	 * Gets the voorletters
	 * @return Returns a String
	 */
	public String getVoorletters()
	{
		return sVoorletters;
	}
	/**
	 * Sets the voorletters
	 * @param voorletters The voorletters to set
	 */
	public void setVoorletters(String voorletters)
	{
		sVoorletters = voorletters;
	}
}
