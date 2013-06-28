/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.security.KOAEncryptionUtil.java
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
  *  0.1		17-04-2003	XU			First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.security;
import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.DataInputStream;
import java.io.DataOutputStream;
import java.io.IOException;
import java.security.InvalidAlgorithmParameterException;
import java.security.InvalidKeyException;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.security.PrivateKey;
import java.security.PublicKey;
import java.sql.Connection;
import java.sql.ResultSet;
import java.sql.ResultSetMetaData;
import java.sql.Statement;
import java.sql.Timestamp;

import javax.crypto.BadPaddingException;
import javax.crypto.Cipher;
import javax.crypto.IllegalBlockSizeException;
import javax.crypto.KeyGenerator;
import javax.crypto.NoSuchPaddingException;
import javax.crypto.SecretKey;
import javax.crypto.spec.IvParameterSpec;

import com.logicacmg.koa.constants.ErrorConstants;
import com.logicacmg.koa.db.BLOBResultSet;
import com.logicacmg.koa.db.DBUtils;
import com.logicacmg.koa.exception.KOAException;
import com.logicacmg.koa.security.FingerPrint;
import com.logicacmg.koa.security.RandomGenerator;
import com.logicacmg.koa.utils.KOALogHelper;
/**
 * Utility class that contains the encryption functionality
 * for the KOA System. 
 * 
 * @author UiterliX
 */
public class KOAEncryptionUtil
{
	private final static String PUBLIC_KEY_CRYPT_ALGO = "RSA";
	private final static String SECRET_KEY_CRYPT_ALGO =
		"DESede/CBC/PKCS5Padding";
	private final static String SECRET_KEY_GENERATOR_ALGO = "DESede";
	/*
	 * CHANGED THE LENGTH FOR PUBLICATION PURPOSES
	 */
	private final static int SECRET_KEY_LENGTH = 999;
	/*
	 * CHANGED THE SALT FOR PUBLICATION PURPOSES
	 */
	private static final byte[] SALT = {(byte) 0x1 };
	private static KeyGenerator xKeyGen;
	/*
	 * CHANGED THE ENCRYPTION KEY FOR PUBLICATION PURPOSES
	 */
	private final static String encryptionKey = "ENCRYPTION_KEY";
	static {
		java.security.Security.addProvider(new iaik.security.provider.IAIK());
	}
	/**
	 * Method to hash the password provided
	 * 
	 * @param password The password to hash
	 * 
	 * @return String The hashed password
	 * 
	 * @throws KOAException when something goes wrong during the hashing of the password.
	 * 
	 */
	public static String hashPassword(String password) throws KOAException
	{
		MessageDigest md = null;
		try
		{
			md = MessageDigest.getInstance("SHA-1");
			md.update(password.getBytes());
		}
		catch (java.security.NoSuchAlgorithmException nse)
		{
			throw new KOAException("ENC-01");
		}
		byte[] output = md.digest();
		StringBuffer sb = new StringBuffer(2 * output.length);
		for (int i = 0; i < output.length; ++i)
		{
			int k = output[i] & 0xFF;
			if (k < 0x10)
				sb.append('0');
			sb.append(Integer.toHexString(k));
		}
		return sb.toString();
	}
	/**
	 * Compares the to fingerprints
	 * 
	 * @param printA The first fingerprint for the comparison
	 * @param printB The second fingerprint for the comparison
	 * 
	 * @return boolean for the result: true if the are equal, false otherwise.
	 * 
	 */
	public static boolean compareFingerprints(byte[] printA, byte[] printB)
	{
		return MessageDigest.isEqual(printA, printB);
	}
	/** 
	 * Compairs two public keys
	 * 
	 * @param keyA public key A
	 * @param keyB public key B 
	 * 
	 * @return boolean 
	 */
	public static boolean comparePublicKey(PublicKey keyA, PublicKey keyB)
	{
		return keyA.equals(keyB);
	}
	/**
	 * encrypts the String with the public key and returns the encrypted data
	 * as a byte array
	 * 
	 * @param xRSAKey	the public key used to crypt the data
	 * @param sData		the data that is cryped
	 * 
	 * @throws KOAException	when the encryption fails for one reason or another
	 * 
	 * @return byte[] the cryped data
	 */
	public static byte[] encrypt(PublicKey xRSAKey, String sData)
		throws KOAException
	{
		try
		{
			// generate triple des key
			if (xKeyGen == null)
			{
				xKeyGen = KeyGenerator.getInstance(SECRET_KEY_GENERATOR_ALGO);
				xKeyGen.init(SECRET_KEY_LENGTH);
			}
			SecretKey xDesKey = xKeyGen.generateKey();
			// generate salt + data
			String sDataToCript =
				RandomGenerator.getInstance().getSalt() + sData;
			// cript key with rsa
			Cipher xCipherKey = Cipher.getInstance(PUBLIC_KEY_CRYPT_ALGO);
			xCipherKey.init(Cipher.WRAP_MODE, xRSAKey);
			byte[] baCriptKey = xCipherKey.wrap(xDesKey);
			//cript salt + tekst
			Cipher xCipherData = Cipher.getInstance(SECRET_KEY_CRYPT_ALGO);
			IvParameterSpec xParamSpec = new IvParameterSpec(SALT);
			xCipherData.init(Cipher.ENCRYPT_MODE, xDesKey, xParamSpec);
			byte[] baCriptData = xCipherData.doFinal(sDataToCript.getBytes());
			// stream triple des key + cript tekst
			ByteArrayOutputStream xByteArrayOutput =
				new ByteArrayOutputStream();
			DataOutputStream xDataOutput =
				new DataOutputStream(xByteArrayOutput);
			// write length of key
			xDataOutput.writeInt(baCriptKey.length);
			// write key
			xDataOutput.write(baCriptKey, 0, baCriptKey.length);
			// write length of key
			xDataOutput.writeInt(baCriptData.length);
			// write cript data
			xDataOutput.write(baCriptData, 0, baCriptData.length);
			// close streams
			xDataOutput.close();
			xByteArrayOutput.close();
			// return byte array (length criptkey + criptkey + length cript data + cript data) 
			return xByteArrayOutput.toByteArray();
		}
		catch (NoSuchAlgorithmException nsae)
		{
			String[] params = { "NoSuchAlgorithmException" };
			KOALogHelper.logErrorCode(
				"KOAEncryptionUtil",
				ErrorConstants.ERR_SECUR_ENCRYPT,
				params,
				nsae);
			throw new KOAException(ErrorConstants.ENCRYPTION_ERROR, nsae);
		}
		catch (InvalidAlgorithmParameterException iape)
		{
			String[] params = { "InvalidAlgorithmParameterException" };
			KOALogHelper.logErrorCode(
				"KOAEncryptionUtil",
				ErrorConstants.ERR_SECUR_ENCRYPT,
				params,
				iape);
			throw new KOAException(ErrorConstants.ENCRYPTION_ERROR, iape);
		}
		catch (IllegalBlockSizeException ibse)
		{
			String[] params = { "IllegalBlockSizeException" };
			KOALogHelper.logErrorCode(
				"KOAEncryptionUtil",
				ErrorConstants.ERR_SECUR_ENCRYPT,
				params,
				ibse);
			throw new KOAException(ErrorConstants.ENCRYPTION_ERROR, ibse);
		}
		catch (BadPaddingException bpe)
		{
			String[] params = { "BadPaddingException" };
			KOALogHelper.logErrorCode(
				"KOAEncryptionUtil",
				ErrorConstants.ERR_SECUR_ENCRYPT,
				params,
				bpe);
			throw new KOAException(ErrorConstants.ENCRYPTION_ERROR, bpe);
		}
		catch (NoSuchPaddingException nspe)
		{
			String[] params = { "NoSuchPaddingException" };
			KOALogHelper.logErrorCode(
				"KOAEncryptionUtil",
				ErrorConstants.ERR_SECUR_ENCRYPT,
				params,
				nspe);
			throw new KOAException(ErrorConstants.ENCRYPTION_ERROR, nspe);
		}
		catch (InvalidKeyException ike)
		{
			String[] params = { "InvalidKeyException" };
			KOALogHelper.logErrorCode(
				"KOAEncryptionUtil",
				ErrorConstants.ERR_SECUR_ENCRYPT,
				params,
				ike);
			throw new KOAException(ErrorConstants.ENCRYPTION_ERROR, ike);
		}
		catch (IOException ioe)
		{
			String[] params = { "data outputstream" };
			KOALogHelper.logErrorCode(
				"KOAEncryptionUtil",
				ErrorConstants.ERR_IO,
				params,
				ioe);
			throw new KOAException(ErrorConstants.ENCRYPTION_ERROR, ioe);
		}
	}
	/**
	 * decrypts the encryped byte aray with the private key and returns decrypted 
	 * data as a String
	 * 
	 * @param xRSAKey the private key used te decrypt the data
	 * @param encryptedBytes the encryped bytearray
	 * 
	 * @throws KOAException when decryption fails for one reason or another
	 * 
	 * @return String the decryped data
	 */
	public static String decrypt(PrivateKey xRSAKey, byte[] encryptedBytes)
		throws KOAException
	{
		try
		{
			// create stream from encrypted bytes
			ByteArrayInputStream xByteArrayInput =
				new ByteArrayInputStream(encryptedBytes);
			DataInputStream xDataInput = new DataInputStream(xByteArrayInput);
			// decrypd key with rsa
			int iKeyLenght = xDataInput.readInt();
			byte[] baCriptKey = new byte[iKeyLenght];
			xDataInput.read(baCriptKey);
			Cipher xCipherKey = Cipher.getInstance(PUBLIC_KEY_CRYPT_ALGO);
			xCipherKey.init(Cipher.UNWRAP_MODE, xRSAKey);
			SecretKey xDesKey =
				(SecretKey) xCipherKey.unwrap(
					baCriptKey,
					SECRET_KEY_GENERATOR_ALGO,
					Cipher.SECRET_KEY);
			// decript salt + data
			Cipher xCipherData = Cipher.getInstance(SECRET_KEY_CRYPT_ALGO);
			IvParameterSpec xParamSpec = new IvParameterSpec(SALT);
			xCipherData.init(Cipher.DECRYPT_MODE, xDesKey, xParamSpec);
			int iDataLenght = xDataInput.readInt();
			byte[] baCriptData = new byte[iDataLenght];
			xDataInput.read(baCriptData);
			byte[] baDecryptedData = xCipherData.doFinal(baCriptData);
			// remove salt from decript tekst.
			return new String(baDecryptedData).substring(
				RandomGenerator.SALT_LENGTE);
		}
		catch (NoSuchAlgorithmException nsae)
		{
			String[] params = { "NoSuchAlgorithmException" };
			KOALogHelper.logErrorCode(
				"KOAEncryptionUtil",
				ErrorConstants.ERR_SECUR_DECRYPT,
				params,
				nsae);
			throw new KOAException(ErrorConstants.DECRYPTION_ERROR, nsae);
		}
		catch (InvalidAlgorithmParameterException iape)
		{
			String[] params = { "InvalidAlgorithmParameterException" };
			KOALogHelper.logErrorCode(
				"KOAEncryptionUtil",
				ErrorConstants.ERR_SECUR_DECRYPT,
				params,
				iape);
			throw new KOAException(ErrorConstants.DECRYPTION_ERROR, iape);
		}
		catch (IllegalBlockSizeException ibse)
		{
			String[] params = { "IllegalBlockSizeException" };
			KOALogHelper.logErrorCode(
				"KOAEncryptionUtil",
				ErrorConstants.ERR_SECUR_DECRYPT,
				params,
				ibse);
			throw new KOAException(ErrorConstants.DECRYPTION_ERROR, ibse);
		}
		catch (BadPaddingException bpe)
		{
			String[] params = { "BadPaddingException" };
			KOALogHelper.logErrorCode(
				"KOAEncryptionUtil",
				ErrorConstants.ERR_SECUR_DECRYPT,
				params,
				bpe);
			throw new KOAException(ErrorConstants.DECRYPTION_ERROR, bpe);
		}
		catch (NoSuchPaddingException nspe)
		{
			String[] params = { "NoSuchPaddingException" };
			KOALogHelper.logErrorCode(
				"KOAEncryptionUtil",
				ErrorConstants.ERR_SECUR_DECRYPT,
				params,
				nspe);
			throw new KOAException(ErrorConstants.DECRYPTION_ERROR, nspe);
		}
		catch (InvalidKeyException ike)
		{
			String[] params = { "InvalidKeyException" };
			KOALogHelper.logErrorCode(
				"KOAEncryptionUtil",
				ErrorConstants.ERR_SECUR_DECRYPT,
				params,
				ike);
			throw new KOAException(ErrorConstants.DECRYPTION_ERROR, ike);
		}
		catch (IOException ioe)
		{
			String[] params = { "data outputstream" };
			KOALogHelper.logErrorCode(
				"KOAEncryptionUtil",
				ErrorConstants.ERR_IO,
				params,
				ioe);
			throw new KOAException(ErrorConstants.DECRYPTION_ERROR, ioe);
		}
	}
	/**
	 * Creates the fingerprint of the provided database table
	 * 
	 * @param datasourceName The datasource to get the fingerprint for
	 * @param schemaName The schema name to get the fingerprint for
	 * @param tableName The table name to get the fingerprint for
	 * @param columns The columns to use in the creation of the fingerprint
	 * @param sortKey the key to sort the rows on
	 * 
	 * @return byte [] containing the fingerprint
	 * 
	 * @throws KOAException when something goes wrong during the creation of the fingerprint.
	 * 
	 */
	public static byte[] getFingerPrint(
		String datasourceName,
		String schemaName,
		String tableName,
		String[] columns,
		String sortKey)
		throws KOAException
	{
		DBUtils db = new DBUtils(datasourceName);
		Connection conn = db.getConnection();
		Statement stmt = null;
		ResultSet rSet = null;
		FingerPrint fPrint = new FingerPrint(encryptionKey);
		try
		{
			stmt = conn.createStatement();
			String cols;
			if (columns.length > 0)
			{
				cols = columns[0];
				if (columns.length > 1)
					for (int i = 1; i < columns.length; i++)
					{
						cols = cols + "," + columns[i];
					}
				String sQuery =
					"SELECT "
						+ cols
						+ " FROM "
						+ schemaName
						+ "."
						+ tableName
						+ " ORDER BY "
						+ sortKey;
				KOALogHelper.log(
					KOALogHelper.TRACE,
					"[KOAEncryptionUtil.getFingerPrint] Query: " + sQuery);
				rSet = stmt.executeQuery(sQuery);
				ResultSetMetaData metadata = rSet.getMetaData();
				while (rSet.next())
				{
					for (int i = 1; i <= columns.length; ++i)
					{
						byte[] tmp = null;
						Timestamp date = null;
						String sTmp = null;
						/* A timestamp cannot be fetched as a byte[] so we have to format it first */
						if (metadata.getColumnType(i)
							== java.sql.Types.TIMESTAMP)
						{
							date = rSet.getTimestamp(columns[i - 1]);
							/* get the time in millis */
							if (date != null)
							{
								tmp = String.valueOf(date.getTime()).getBytes();
							}
							else
							{
								tmp = null;
							}
							/* Other rows can be fetched as a byte[] */
						}
						else
						{
							tmp = rSet.getBytes(columns[i - 1]);
						}
						if (tmp != null)
						{
							sTmp = new String(tmp);
							fPrint.update(tmp);
						}
					}
				}
			}
			else
			{
				KOALogHelper.log(
					KOALogHelper.TRACE,
					"[KOAEncryptionUtil.getFingerPrint] No columns specified");
				throw new KOAException("ENC-02");
			}
		}
		catch (java.sql.SQLException sqle)
		{
			KOALogHelper.log(KOALogHelper.TRACE, sqle.getMessage());
			throw new KOAException("ENC-03");
		}
		catch (Exception e)
		{
			e.printStackTrace();
		}
		finally
		{
			db.closeResultSet(rSet);
			db.closeStatement(stmt);
			db.closeConnection(conn);
		}
		byte[] bDigest = null;
		bDigest = fPrint.getDigest();
		StringBuffer sb = new StringBuffer(2 * bDigest.length);
		for (int i = 0; i < bDigest.length; ++i)
		{
			int k = bDigest[i] & 0xFF;
			if (k < 0x10)
				sb.append('0');
			sb.append(Integer.toHexString(k));
		}
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[KOAEncryptionUtil.getFingerPrint] Calculated fingerprint: "
				+ sb.toString());
		return sb.toString().getBytes();
	}
	/**
	 * Creates the fingerprint of the provided database table. Special method for tables containing blobs
	 * 
	 * @param datasourceName The datasource to get the fingerprint for
	 * @param schemaName The schema name to get the fingerprint for
	 * @param tableName The table name to get the fingerprint for
	 * @param columns The columns to use in the creation of the fingerprint
	 * @param sortKey the key to sort the rows on
	 * 
	 * @return byte [] containing the fingerprint
	 * 
	 * @throws KOAException when something goes wrong during the creation of the fingerprint.
	 * 
	 */
	public static byte[] getBLOBFingerPrint(
		String datasourceName,
		String schemaName,
		String tableName,
		String[] columns,
		String sortKey)
		throws KOAException
	{
		DBUtils db = new DBUtils(datasourceName);
		Connection conn = db.getConnection();
		Statement stmt = null;
		BLOBResultSet rSet = null;
		FingerPrint fPrint = new FingerPrint(encryptionKey);
		try
		{
			stmt = conn.createStatement();
			String cols;
			if (columns.length > 0)
			{
				rSet =
					new BLOBResultSet(
						datasourceName,
						schemaName,
						tableName,
						sortKey,
						columns);
				KOALogHelper.log(
					KOALogHelper.TRACE,
					"[KOAEncryptionUtil.getFingerPrint] Using BLOBResultSet");
				while (rSet.next())
				{
					for (int i = 1; i <= columns.length; ++i)
					{
						byte[] tmp = null;
						Timestamp date = null;
						String sTmp = null;
						/* Other rows can be fetched as a byte[] */
						tmp = rSet.getBytes(columns[i - 1]);
						if (tmp != null)
						{
							sTmp = new String(tmp);
							fPrint.update(tmp);
						}
					}
				}
			}
			else
			{
				KOALogHelper.log(
					KOALogHelper.TRACE,
					"[KOAEncryptionUtil.getFingerPrint] No columns specified");
				throw new KOAException("ENC-02");
			}
		}
		catch (Exception e)
		{
			KOALogHelper.log(KOALogHelper.TRACE, e.getMessage());
			throw new KOAException("ENC-03");
		}
		finally
		{
			rSet.close();
		}
		byte[] bDigest = null;
		bDigest = fPrint.getDigest();
		StringBuffer sb = new StringBuffer(2 * bDigest.length);
		for (int i = 0; i < bDigest.length; ++i)
		{
			int k = bDigest[i] & 0xFF;
			if (k < 0x10)
				sb.append('0');
			sb.append(Integer.toHexString(k));
		}
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[KOAEncryptionUtil.getFingerPrint] Calculated fingerprint: "
				+ sb.toString());
		return sb.toString().getBytes();
	}
	/**
	 * Translate the byte array of the fingerprint to a comparable format
	 * 
	 * @param baBytes byte array containing the fingerprint
	 * 
	 * @return String the string representation of the fingerprint
	 * 
	 */
	public static String fingerprintValueToString(byte[] baBytes)
	{
		if (baBytes == null)
		{
			return "";
		}
		String s = new String(baBytes);
		return s;
	}
}