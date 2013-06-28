/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.dataobjects.CallResult
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
  *  0.1		14-04-2003	AGr	        First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.dataobjects;
import java.io.Serializable;
/**
 * This class is used as a return value of a number of methods
 */
public class CallResult implements Serializable
{
	/****************************************************************
	 * 						CONSTANTS 								*
	 ****************************************************************/
	public final static String NOT_NUMERIC = "De pincode is niet numeriek";
	public final static String NOT_CORRECT_LENGTH =
		"De pincode bestaat niet uit 5 karakters";
	public final static String NOT_UNIQUE = "De pincodes zijn niet uniek!";
	public final static String NOT_EXIST =
		"De ingevoerde pincode(s) is/zijn onjuist";
	public final static String PINCODE_ERROR =
		"Er heeft zich een probleem voorgedaan tijdens het ophalen van de pincode uit de database.";
	public final static String EMPTY_FIELD = "De pincode is niet ingevuld";
	public final static String EMPTY_PUBLIC_KEY =
		"De publickey is leeg gelaten";
	/**
	 * constants returned when the static KR has invalid fingerprints
	 * 
	 */
	public final static int FINGERPRINTS_STAT_KR_ERR = -2;
	/**
	 * constants returned when the static KR has invalid fingerprints
	 * 
	 */
	public final static int FINGERPRINTS_DYN_KR_ERR = -1;
	/**
	 * fingerprints of KR are OK
	 * 
	 */
	public final static int FINGERPRINTS_OK = 1;
	/**
	 * an error has occurred while executing method
	 * 
	 */
	public final static int ERROR_DURING_CALL = -4;
	/**
	 * everything is fine
	 * 
	 */
	public final static int RESULT_OK = 2;
	/**
	 * the fingerprint of the ESB is OK
	 * 
	 */
	public final static int FINGERPRINT_ESB_OK = 3;
	/**
	 * the fingerprint in the ESB is invalid
	 * 
	 */
	public final static int FINGERPRINT_ESB_ERR = -3;
	/**
	 * error when the ESB is not empty at initialise
	 * 
	 */
	public final static int ESB_NOT_EMPTY = -5;
	/**
	 * error when the KR is not filled at initialise
	 * 
	 */
	public final static int KR_NOT_FILLED = -8;
	/**
	 * error when the indication voted isn't deleted
	 * 
	 */
	public final static int KR_INIDCATION_VOTED_FILLED = -9;
	/**
	 * error when the indication voted isn't deleted
	 * 
	 */
	public final static int KR_TIMESTAMP_VOTING_FILLED = -10;
	/**
	 * error when the column modaliteit isn't empty
	 * 
	 */
	public final static int KR_MODALITEIT_FILLED = -12;
	/**
	 * unknown result 
	 * 
	 */
	public final static int RESULT_UNKNOWN = -4;
	/**
	 * Result parameter when the overall state change went succesful
	 * 
	 */
	public final static int STATE_CHANGE_SUCCESFUL = 6;
	/**
	 * Result parameter when the overall state change did not go succesful for 
	 * one or more components.
	 * 
	 */
	public final static int STATE_CHANGE_INVALID = -6;
	public final static int NOTIFY_STATE_CHANGE_INVALID_FINGERPRINTS = -14;
	/**
	 * Result parameter when the overall state change did go succesful for 
	 * a single component.
	 * 
	 */
	public final static int NOTIFY_STATE_CHANGE_SUCCESFUL = 7;
	/**
	 * Result parameter when the overall state change did not go succesful for 
	 * a single component.
	 * 
	 */
	public final static int NOTIFY_STATE_CHANGE_ERROR = -7;
	/**
	 * Result parameter when the overall state change did not go succesful for 
	 * a notifying the state to the WSM or TSM.
	 * 
	 */
	public final static int NOTIFY_STATE_CHANGE_WARNING = -8;
	/**
	 * Result parameter when the public keys are not the same.
	 * 
	 */
	public final static int PUBLIC_KEYS_NOT_SAME = -11;
	/**
	 * OR 22.3.602
	 * Result parameter when pincodes are the same.
	 * 
	 */
	public final static int PINCODE_NOT_UNIQUE = -15;
	/**
	 * OR 22.3.602
	 * Result parameter when pincode has not the correct length.
	 * 
	 */
	public final static int PINCODE_NOT_CORRECT_LENGTH = -16;
	/**
	 * OR 22.3.602
	 * Result parameter when pincode has not a numeric value.
	 * 
	 */
	public final static int PINCODE_NOT_NUMERIC = -17;
	/**
	 * OR 22.3.602
	 * Result parameter when pincode not exist.
	 * 
	 */
	public final static int PINCODE_NOT_EXIST = -18;
	/**
	 * OR 22.3.602
	 * Result parameter when pincode is empty.
	 * 
	 */
	public final static int PINCODE_EMPTY = -19;
	/**
	 * OR 22.3.602
	 * Result parameter when the public key is empty.
	 * 
	 */
	public final static int PUBLIC_KEY_EMPTY = -11;
	private int g_iResult;
	private String g_sMessage = null;
	;
	private String g_sCurrentState = null;
	private java.util.Vector g_vUnsuccesfullComponents = null;
	private String g_sBackupResult = "";
	public int getResult()
	{
		return g_iResult;
	}
	public void setResult(int iResult)
	{
		g_iResult = iResult;
	}
	public void setMessage(String sMessage)
	{
		g_sMessage = sMessage;
	}
	public String getMessage()
	{
		return g_sMessage;
	}
	public void setCurrentState(String sState)
	{
		g_sCurrentState = sState;
	}
	public String getCurrentState()
	{
		return g_sCurrentState;
	}
	public void addUnsuccesfullComponentType(String sComponentType)
	{
		if (g_vUnsuccesfullComponents == null)
		{
			g_vUnsuccesfullComponents = new java.util.Vector();
		}
		g_vUnsuccesfullComponents.add(sComponentType);
	}
	public java.util.Vector getUnsuccesfullComponents()
	{
		if (g_vUnsuccesfullComponents == null)
		{
			return new java.util.Vector();
		}
		else
		{
			return g_vUnsuccesfullComponents;
		}
	}
	public String getBackupResult()
	{
		return g_sBackupResult;
	}
	public void setBackupResult(String sBackupResult)
	{
		g_sBackupResult = sBackupResult;
	}
}