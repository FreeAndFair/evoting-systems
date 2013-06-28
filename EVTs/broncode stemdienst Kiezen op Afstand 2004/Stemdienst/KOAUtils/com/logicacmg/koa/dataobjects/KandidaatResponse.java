/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.dataobjects.KandidaatResponse.java
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
  *  0.1		18-04-2003	AGr	        First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.dataobjects;

import com.logicacmg.koa.dataobjects.Kandidaat;

/**
  * Data object used by the Kieslijstbean
  */
public class KandidaatResponse implements java.io.Serializable
{
	//error occured while retrieving a kandidaat
	public final static int KANDIDATE_ERR = -1;
	//unkown status
	public final static int STATUS_UNKNOWN = 0;
	//candidate is OK
	public final static int KANDIDATE_OK = 1;
	//candidate is not found
	public final static int KANDIDATE_NOT_FOUND = 2;
	//candidate cannot be found: elections are closed
	public final static int ELECTION_NOT_YET_OPEN = 3;
	public final static int ELECTION_CLOSED = 4;
	public final static int ELECTION_BLOCKED = 5;
	public final static int ELECTION_SUSPENDED = 6;
	public final static int KANDIDATE_NOT_NUMERIC = 7;
	public final static int KANDIDATE_NOT_CORRECT_LENGTH = 8;
	public Kandidaat kandidaat = null;
	public String kandidaatcode;
	public int status = STATUS_UNKNOWN;
	/**
	 * Gets the kandidaat
	 * @return Returns a Kandidaat
	 */
	public Kandidaat getKandidaat()
	{
		return kandidaat;
	}
	/**
	 * Sets the kandidaat
	 * @param kandidaat The kandidaat to set
	 */
	public void setKandidaat(Kandidaat kandidaat)
	{
		this.kandidaat = kandidaat;
	}
}
