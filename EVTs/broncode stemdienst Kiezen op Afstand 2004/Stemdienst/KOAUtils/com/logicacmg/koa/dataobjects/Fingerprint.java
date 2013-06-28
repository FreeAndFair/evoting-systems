/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.dataobjects.Fingerprint
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
  *  0.1		16-04-2003	AGr	        First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.dataobjects;
/**
 * Data object that contains data regarding to a fingerprint
 */
public class Fingerprint implements java.io.Serializable
{
	//constants
	public final static short FINGERPRINT_TYPE_UNKNOWN = -1;
	public final static short ESB_FINGERPRINT = 0;
	public final static short KR_STATIC_FINGERPRINT = 1;
	public final static short KR_DYNAMIC_FINGERPRINT = 2;
	public final static short KIESLIJST_KANDIDAATCODES_FINGERPRINT = 3;
	public final static short KIESLIJST_LIJSTPOSITIES_FINGERPRINT = 4;
	public final static short KIESLIJST_KIESLIJSTEN_FINGERPRINT = 5;
	private byte[] g_Fingerprint;
	private java.sql.Timestamp g_xTimestamp;
	//type of fingerprint
	private int g_iType = FINGERPRINT_TYPE_UNKNOWN;
	//access methods
	public byte[] getFingerprint()
	{
		return g_Fingerprint;
	}
	public void setFingerprint(byte[] newFingerprint)
	{
		this.g_Fingerprint = newFingerprint;
	}
	public int getFingerprintType()
	{
		return g_iType;
	}
	public void setFingerprintType(int iNewType)
	{
		this.g_iType = iNewType;
	}
	public java.sql.Timestamp getTimestamp()
	{
		return g_xTimestamp;
	}
	public void setTimestamp(java.sql.Timestamp xTimestamp)
	{
		this.g_xTimestamp = xTimestamp;
	}
	public boolean equals(Fingerprint xEqualsFingerprint)
	{
		if (xEqualsFingerprint == null)
		{
			return false;
		}
		return java.util.Arrays.equals(
			g_Fingerprint,
			xEqualsFingerprint.getFingerprint());
	}
	public int hashcode()
	{
		// Hashcode is the addition of the first 8 bytes.
		int result = 0;
		for (int i = 0; i < g_Fingerprint.length && i < 8; i++)
		{
			result += g_Fingerprint[i];
		}
		return result;
	}
}