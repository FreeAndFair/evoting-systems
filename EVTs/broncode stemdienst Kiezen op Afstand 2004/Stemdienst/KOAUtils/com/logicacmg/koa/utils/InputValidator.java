/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.utils.InputValidator.java
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
  *  0.2.0.5	04-11-2003	XUi/MKu		First implementation for empty candidatecode
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.utils;
import com.logicacmg.koa.utils.KOALogHelper;
/**
 * Class to validate the input parameters. 
 */
public class InputValidator
{
	/**
	 * Validate the candidate code on null, empty, digits and length.
	 * 
	 * @param String The code to check
	 * 
	 * @return boolean indicating the result
	 */
	public static boolean validateCandidate(String candidateCode)
	{
		/*
		 * If the kandidaatcode is not present (null or empty)
		 * we return immediately
		 */
		if (candidateCode == null || candidateCode.equals(""))
		{
			KOALogHelper.log(
				KOALogHelper.ERROR,
				"[InputValidator.validateCandidate] Candidatecode is null or empty.");
			return false;
		}
		char cCharFromKandidaatcode;
		for (int i = 0; i < candidateCode.length(); i++)
		{
			cCharFromKandidaatcode = candidateCode.charAt(i);
			// check if character is numeric
			if (!Character.isDigit(cCharFromKandidaatcode))
			{
				KOALogHelper.log(
					KOALogHelper.ERROR,
					"[InputValidator.validateCandidate] Candidatecode is not a number.");
				return false;
			}
		}
		if (candidateCode.length() != 9)
		{
			KOALogHelper.log(
				KOALogHelper.ERROR,
				"[InputValidator.validateCandidate] Candidatecode has incorrect length.");
			return false;
		}
		return true;
	}
	/**
	 * Validate the stemcode/password combi
	 * 
	 * @param String the stemcode to check
	 * @param String the password to check
	 * 
	 * @return boolean indicating the result
	 */
	public static boolean validateUser(String stemcode, String password)
	{
		if (stemcode == null || "".equals(stemcode))
		{
			KOALogHelper.log(
				KOALogHelper.ERROR,
				"[InputValidator.validateUser] stemcode is null or empty.");
			return false;
		}
		if (password == null || "".equals(password))
		{
			KOALogHelper.log(
				KOALogHelper.ERROR,
				"[InputValidator.validateUser] password is null or empty.");
			return false;
		}
		char cCharFromStemcode;
		for (int i = 0; i < stemcode.length(); i++)
		{
			cCharFromStemcode = stemcode.charAt(i);
			// check if character is numeric
			if (!Character.isDigit(cCharFromStemcode))
			{
				KOALogHelper.log(
					KOALogHelper.ERROR,
					"[InputValidator.validateUser] stemcode is not a number.");
				return false;
			}
		}
		if (stemcode.length() != 9)
		{
			KOALogHelper.log(
				KOALogHelper.ERROR,
				"[InputValidator.validateUser] stemcode has incorrect length.");
			return false;
		}
		char cCharFromPassword;
		for (int i = 0; i < password.length(); i++)
		{
			cCharFromPassword = password.charAt(i);
			// check if character is numeric
			if (!Character.isDigit(cCharFromPassword))
			{
				KOALogHelper.log(
					KOALogHelper.ERROR,
					"[InputValidator.validateUser] password is not a number.");
				return false;
			}
		}
		return true;
	}
}
