/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.security.RandomGenerator.java
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
  *  0.1		18-04-2003	MRo			First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.security;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.security.NoSuchAlgorithmException;
import java.security.SecureRandom;

import com.logicacmg.koa.exception.KOAException;
/**
 * Generates random numbers
 * 
 * @author MRo
 */
public class RandomGenerator
{
	private SecureRandom random;
	private static RandomGenerator instance;
	private static final String RANDOM_ALGORITHM = "SHA1PRNG";
	private static final int MAX_RANDOM_POWER = 32;
	private static final int KANDIDAATCODE_LENGTE = 9;
	private static final int KIEZERSCODE_LENGTE = 9;
	private static final int TRANSACTIECODE_LENGTE = 9;
	/*
	 * CHANGED THE SALT_LENGTE FOR PUBLICATION PURPOSES
	 */
	public static final int SALT_LENGTE = 999;
	private float fMaxValue;
	/**
	 * Constructor
	 * 
	 * @throws KOAException when something goes wrong during constructing of the Generator
	 * 
	 */
	private RandomGenerator() throws KOAException
	{
		try
		{
			random = SecureRandom.getInstance(RANDOM_ALGORITHM);
			fMaxValue =
				BigInteger.valueOf(2).pow(MAX_RANDOM_POWER).floatValue();
		}
		catch (NoSuchAlgorithmException nsae)
		{
			throw new KOAException("ENC-01");
		}
	}
	/**
	 * Private method to get the instance, to make sure 
	 * there will be only one RandomGenerator instance
	 * 
	 * @return RandomGenerator the instance of RandomGenerator
	 * 
	 * @throws KOAException when anything goes wrong during the get instance
	 */
	public static RandomGenerator getInstance() throws KOAException
	{
		if (instance == null)
		{
			instance = new RandomGenerator();
		}
		return instance;
	}
	/**
	 * Generates a random kandidaat code (code is 11-proef)
	 * 
	 * @return String random kandidaat code
	 */
	public String getKandidaatCode()
	{
		return getCode(KANDIDAATCODE_LENGTE);
	}
	/**
	 * Generates a random kiezers code (code is 11-proef)
	 * 
	 * @return String random kiezers code
	 */
	public String getKiezersCode()
	{
		return getCode(KIEZERSCODE_LENGTE);
	}
	/**
	 * Generates a random transactie code (code is 11-proef)
	 * 
	 * @return String random transactie code
	 */
	public String getTransactieCode()
	{
		return getCode(TRANSACTIECODE_LENGTE);
	}
	/**
	 * Generates a random code (code is 11-proef)
	 * 
	 * @return String random  code
	 */
	private String getCode(int iLength)
	{
		// Get a random number as a string
		String sExtraChar = null;
		String sNumber = null;
		boolean bNotOk = true;
		while (bNotOk == true)
		{
			bNotOk = false;
			sExtraChar = null;
			sNumber = getRandomNumber(iLength - 1).toString();
			// Generate the last digit to be correct according to the 11-proef
			// Calculate the sum of 7 x first digit + 6 x second digit and so on
			// only the final calculation 1 x final digit will be "-1 x final digit"
			// this is the diverance between bank account 11-proef and sofi 11 proef
			double sum = 0;
			int digit = 0;
			for (int i = iLength - 1; i > 0; i = i - 1)
			{
				digit =
					Integer
						.valueOf(
							sNumber.substring(iLength - i - 1, iLength - i))
						.intValue();
				sum = sum + (i + 1) * digit;
			}
			// now calculate the mod 11 on the sum
			int dMod = new Double(sum % 11).intValue();
			if (dMod == 10)
			{
				bNotOk = true;
			}
			else
			{
				sExtraChar = String.valueOf(dMod);
			}
		}
		return sNumber + sExtraChar;
	}
	/**
	 * Generates a random number (Salt)
	 * 
	 * @return String random number
	 */
	public String getSalt()
	{
		return getRandomNumber(SALT_LENGTE).toString();
	}
	/**
	 * Generates a random number
	 * 
	 * @param length The length of the random number in characters
	 */
	public BigDecimal getRandomNumber(int length)
	{
		Double dPow = new Double(Math.pow(10, length - 1));
		Double dMultiplier = new Double(dPow.doubleValue() * 9 - 1);
		Float fRandom =
			new Float(
				new BigInteger(MAX_RANDOM_POWER, random).floatValue()
					/ fMaxValue
					* dMultiplier.floatValue()
					+ dPow.floatValue());
		return BigDecimal.valueOf(fRandom.longValue());
	}
}