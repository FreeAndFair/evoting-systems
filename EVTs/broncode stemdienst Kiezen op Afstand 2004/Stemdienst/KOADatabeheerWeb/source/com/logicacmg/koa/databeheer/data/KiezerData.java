/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.databeheer.data.KiezerData.java
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
package com.logicacmg.koa.databeheer.data;
import java.io.Serializable;
/**
 * Data class that wraps the insert data for a nieuw kiezer
 * It als indicates if the is an error with the data
 */
public class KiezerData implements Serializable
{
	private String sKieskring;
	private String sDistrict;
	private String sKiezer;
	private String sHashedWW;
	private boolean bErrorKieskring = false;
	private boolean bErrorDistrict = false;
	/**
	 * Set the kieskringID
	 * 
	 * @param sKieskring kieskringID
	 */
	public void setKieskring(String sKieskring)
	{
		this.sKieskring = sKieskring;
	}
	/**
	 * Set the DistrictID
	 * 
	 * @param sDistrict DistrictID
	 */
	public void setDistrict(String sDistrict)
	{
		this.sDistrict = sDistrict;
	}
	/**
	 * Set the KiezerID
	 * 
	 * @param sKiezer KiezerID
	 */
	public void setKiezer(String sKiezer)
	{
		this.sKiezer = sKiezer;
	}
	/**
	 * Set the HashedWW
	 * 
	 * @param sHashedWW HashedWW
	 */
	public void setHashedWW(String sHashedWW)
	{
		this.sHashedWW = sHashedWW;
	}
	/**
	 * Get the KieskingID
	 * 
	 * @return String KieskingID
	 */
	public String getKieskring()
	{
		return sKieskring;
	}
	/**
	 * Get the DistrictID
	 * 
	 * @return String DistrictID
	 */
	public String getDistrict()
	{
		return sDistrict;
	}
	/**
	 * Get the KiezerID
	 * 
	 * @return String KiezerID
	 */
	public String getKiezer()
	{
		return sKiezer;
	}
	/**
	 * Get the HashedWW
	 * 
	 * @return String HashedWW
	 */
	public String getHashedWW()
	{
		return sHashedWW;
	}
	/**
	 * Indicates if there is an error with Kieskring data
	 * 
	 * @return boolean 
	 */
	public boolean getErrorKieskring()
	{
		return bErrorKieskring;
	}
	/**
	 * set an kieskring error if there is an error in kieskingID
	 */
	public void setErrorKieskring()
	{
		this.bErrorKieskring = true;
	}
	/**
	 * Indicates if there is an error with District data
	 * 
	 * @return boolean 
	 */
	public boolean getErrorDistrict()
	{
		return bErrorDistrict;
	}
	/**
	 * set an District error if there is an error in DistrictID
	 */
	public void setErrorDistrict()
	{
		this.bErrorKieskring = true;
	}
}
