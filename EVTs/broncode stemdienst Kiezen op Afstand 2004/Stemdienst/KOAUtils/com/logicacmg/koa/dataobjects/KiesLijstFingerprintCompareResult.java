package com.logicacmg.koa.dataobjects;
import java.io.Serializable;

import com.logicacmg.koa.security.KOAEncryptionUtil;
public class KiesLijstFingerprintCompareResult implements Serializable
{
	private int iResult = 0;
	private String sMessage = null;
	private String sKandidaatcodesDatabaseFP = null;
	private String sLijstpositiesDatabaseFP = null;
	private String sKieslijstDatabaseFP = null;
	private String sKandidaatcodesCurrentFP = null;
	private String sLijstpositiesCurrentFP = null;
	private String sKieslijstCurrentFP = null;
	private boolean bKandidaatCodeFPEqual = false;
	private boolean bLijstpositiesFPEqual = false;
	private boolean bKieslijstFPEqual = false;
	public final static int KIESLIJST_ALL_FINGERPRINTS_EQUAL = 0;
	public final static int KIESLIJST_NOT_ALL_FINGERPRINT_EQUAL = -1;
	/**
	 * Gets the result
	 * @return Returns a int
	 */
	public int getResult()
	{
		return iResult;
	}
	/**
	 * Sets the result
	 * @param result The result to set
	 */
	public void setResult(int result)
	{
		iResult = result;
	}
	/**
	 * Gets the message
	 * @return Returns a String
	 */
	public String getMessage()
	{
		return sMessage;
	}
	/**
	 * Sets the message
	 * @param message The message to set
	 */
	public void setMessage(String message)
	{
		sMessage = message;
	}
	/**
	 * Gets the kandidaatcodesDatabaseFP
	 * @return Returns a String
	 */
	public String getKandidaatcodesDatabaseFP()
	{
		return sKandidaatcodesDatabaseFP;
	}
	/**
	 * Sets the kandidaatcodesDatabaseFP
	 * @param kandidaatcodesDatabaseFP The kandidaatcodesDatabaseFP to set
	 */
	public void setKandidaatcodesDatabaseFP(byte[] kandidaatcodesDatabaseFP)
	{
		sKandidaatcodesDatabaseFP =
			KOAEncryptionUtil.fingerprintValueToString(
				kandidaatcodesDatabaseFP);
	}
	/**
	 * Gets the lijstpositiesDatabaseFP
	 * @return Returns a String
	 */
	public String getLijstpositiesDatabaseFP()
	{
		return sLijstpositiesDatabaseFP;
	}
	/**
	 * Sets the lijstpositiesDatabaseFP
	 * @param lijstpositiesDatabaseFP The lijstpositiesDatabaseFP to set
	 */
	public void setLijstpositiesDatabaseFP(byte[] lijstpositiesDatabaseFP)
	{
		sLijstpositiesDatabaseFP =
			KOAEncryptionUtil.fingerprintValueToString(lijstpositiesDatabaseFP);
	}
	/**
	 * Gets the kieslijstDatabaseFP
	 * @return Returns a String
	 */
	public String getKieslijstDatabaseFP()
	{
		return sKieslijstDatabaseFP;
	}
	/**
	 * Sets the kieslijstDatabaseFP
	 * @param kieslijstDatabaseFP The kieslijstDatabaseFP to set
	 */
	public void setKieslijstDatabaseFP(byte[] kieslijstDatabaseFP)
	{
		sKieslijstDatabaseFP =
			KOAEncryptionUtil.fingerprintValueToString(kieslijstDatabaseFP);
	}
	/**
	 * Gets the kandidaatcodesCurrentFP
	 * @return Returns a String
	 */
	public String getKandidaatcodesCurrentFP()
	{
		return sKandidaatcodesCurrentFP;
	}
	/**
	 * Sets the kandidaatcodesCurrentFP
	 * @param kandidaatcodesCurrentFP The kandidaatcodesCurrentFP to set
	 */
	public void setKandidaatcodesCurrentFP(byte[] kandidaatcodesCurrentFP)
	{
		sKandidaatcodesCurrentFP =
			KOAEncryptionUtil.fingerprintValueToString(kandidaatcodesCurrentFP);
	}
	/**
	 * Gets the lijstpositiesCurrentFP
	 * @return Returns a String
	 */
	public String getLijstpositiesCurrentFP()
	{
		return sLijstpositiesCurrentFP;
	}
	/**
	 * Sets the lijstpositiesCurrentFP
	 * @param lijstpositiesCurrentFP The lijstpositiesCurrentFP to set
	 */
	public void setLijstpositiesCurrentFP(byte[] lijstpositiesCurrentFP)
	{
		sLijstpositiesCurrentFP =
			KOAEncryptionUtil.fingerprintValueToString(lijstpositiesCurrentFP);
	}
	/**
	 * Gets the kieslijstCurrentFP
	 * @return Returns a String
	 */
	public String getKieslijstCurrentFP()
	{
		return sKieslijstCurrentFP;
	}
	/**
	 * Sets the kieslijstCurrentFP
	 * @param kieslijstCurrentFP The kieslijstCurrentFP to set
	 */
	public void setKieslijstCurrentFP(byte[] kieslijstCurrentFP)
	{
		sKieslijstCurrentFP =
			KOAEncryptionUtil.fingerprintValueToString(kieslijstCurrentFP);
	}
	/**
	 * Gets the kandidaatCodeFPEqual
	 * @return Returns a boolean
	 */
	public boolean getKandidaatCodeFPEqual()
	{
		return bKandidaatCodeFPEqual;
	}
	/**
	 * Sets the kandidaatCodeFPEqual
	 * @param kandidaatCodeFPEqual The kandidaatCodeFPEqual to set
	 */
	public void setKandidaatCodeFPEqual(boolean kandidaatCodeFPEqual)
	{
		bKandidaatCodeFPEqual = kandidaatCodeFPEqual;
	}
	/**
	 * Gets the lijstpositiesFPEqual
	 * @return Returns a boolean
	 */
	public boolean getLijstpositiesFPEqual()
	{
		return bLijstpositiesFPEqual;
	}
	/**
	 * Sets the lijstpositiesFPEqual
	 * @param lijstpositiesFPEqual The lijstpositiesFPEqual to set
	 */
	public void setLijstpositiesFPEqual(boolean lijstpositiesFPEqual)
	{
		bLijstpositiesFPEqual = lijstpositiesFPEqual;
	}
	/**
	 * Gets the kieslijstFPEqual
	 * @return Returns a boolean
	 */
	public boolean getKieslijstFPEqual()
	{
		return bKieslijstFPEqual;
	}
	/**
	 * Sets the kieslijstFPEqual
	 * @param kieslijstFPEqual The kieslijstFPEqual to set
	 */
	public void setKieslijstFPEqual(boolean kieslijstFPEqual)
	{
		bKieslijstFPEqual = kieslijstFPEqual;
	}
}
