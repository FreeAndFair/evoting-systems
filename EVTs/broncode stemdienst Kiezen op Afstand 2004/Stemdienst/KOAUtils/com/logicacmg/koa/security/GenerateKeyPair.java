/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.security.GenerateKeyPair.java
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
  *  0.1		12-05-2003	MRo			First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.security;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.security.GeneralSecurityException;
import java.security.InvalidKeyException;
import java.security.Key;
import java.security.KeyPair;
import java.security.KeyPairGenerator;
import java.security.PrivateKey;
import java.security.PublicKey;

import javax.crypto.Cipher;
import javax.crypto.SecretKey;
import javax.crypto.SecretKeyFactory;
import javax.crypto.spec.PBEKeySpec;
import javax.crypto.spec.PBEParameterSpec;

import com.logicacmg.koa.constants.TechnicalProps;
import com.logicacmg.koa.exception.KOAException;
import com.logicacmg.koa.utils.KOALogHelper;
/**
 * main application for the keypair generation
 * 
 * @author Mro
 */
public class GenerateKeyPair
{
	public static final int PRIVATE_KEY = Cipher.PRIVATE_KEY;
	public static final int PUBLIC_KEY = Cipher.PUBLIC_KEY;
	private static final String KEYPAIR_GENERATOR_ALGORITHM = "RSA";
	private int KEYPAIR_KEY_LENGTH = -1;
	private static final String KEY_ENCRIPTION_AKGORITHM = "PBEWithMD5AndDES";
	/*
	 * CHANGED THE SALT FOR PUBLICATION PURPOSES
	 */
	private static final byte[] SALT = {(byte) 0x1 };
	// the wrapped key pair
	private KeyPair keyPair;
	/**
	 * Zero argument constructor for generation a key pair
	 * There will be a public key and a private key available
	 * 
	 * @throws GeneralSecurityException This exception will be thrown when there is a problem with generation a key pair
	 */
	public GenerateKeyPair() throws GeneralSecurityException
	{
		try
		{
			KEYPAIR_KEY_LENGTH =
				TechnicalProps.getIntProperty(TechnicalProps.RSA_KEY_LENGTH);
		}
		catch (KOAException koae)
		{
			KOALogHelper.logError(
				"GenerateKeyPair",
				"Could not obtain the Property "
					+ TechnicalProps.RSA_KEY_LENGTH
					+ " in the Technical.properties. This must be a integer value. For instance 512.",
				koae);
			throw new GeneralSecurityException();
		}
		KeyPairGenerator keyPairGen =
			KeyPairGenerator.getInstance(KEYPAIR_GENERATOR_ALGORITHM);
		keyPairGen.initialize(KEYPAIR_KEY_LENGTH);
		keyPair = keyPairGen.generateKeyPair();
	}
	/** 
	 * Constructor for decryption of a key. 
	 * Only the public of private key of the <code>keyType</code> will be available the other will return null
	 * 
	 * @param password The password used for decryption
	 * @param criptKey A stream with the encrypted key
	 * @param keyType The type of the key public (<code>PUBLIC_KEY</code>) or private (<code>PRIVATE_KEY</code>)
	 * 
	 * @throws GeneralSecurityException This exception will be thrown when there is a problem with decryption
	 * @throws IOException				This exception will be thrown when there is a problem with the stream
	 */
	public GenerateKeyPair(String password, InputStream cryptKey, int keyType)
		throws GeneralSecurityException, IOException
	{
		PBEParameterSpec paramSpec = new PBEParameterSpec(SALT, 20);
		PBEKeySpec keySpec = new PBEKeySpec(password.toCharArray());
		SecretKeyFactory kf =
			SecretKeyFactory.getInstance(KEY_ENCRIPTION_AKGORITHM);
		SecretKey passwordKey = kf.generateSecret(keySpec);
		Cipher cipher = Cipher.getInstance(KEY_ENCRIPTION_AKGORITHM);
		cipher.init(Cipher.UNWRAP_MODE, passwordKey, paramSpec);
		byte[] dummy = new byte[128];
		int length;
		ByteArrayOutputStream byteArray = new ByteArrayOutputStream();
		while ((length = cryptKey.read(dummy)) != -1)
		{
			byteArray.write(dummy, 0, length);
		}
		if (keyType == PRIVATE_KEY)
		{
			Key unwrappedKey =
				cipher.unwrap(
					byteArray.toByteArray(),
					KEYPAIR_GENERATOR_ALGORITHM,
					keyType);
			keyPair = new KeyPair(null, (PrivateKey) unwrappedKey);
		}
		else if (keyType == PUBLIC_KEY)
		{
			Key unwrappedKey =
				cipher.unwrap(
					byteArray.toByteArray(),
					KEYPAIR_GENERATOR_ALGORITHM,
					keyType);
			keyPair = new KeyPair((PublicKey) unwrappedKey, null);
		}
		else
		{
			throw new InvalidKeyException("criptKey does not represent a wrapped key of type keyType");
		}
	}
	/**
	 * Returns a private key if available otherwise it returns null
	 * 
	 * @return PrivateKey private key
	 */
	public PrivateKey getPrivateKey()
	{
		return keyPair.getPrivate();
	}
	/**
	 * Returns a public key if available otherwise it returns null
	 * 
	 * @return PublicKey public key
	 */
	public PublicKey getPublicKey()
	{
		return keyPair.getPublic();
	}
	/**
	 * Encrypted the public key with a password and returns the encypted key with the outputstream
	 * 
	 * @param password The password used for encryption
	 * @param output The encrypted key
	 * 
	 * @throws IOException This exception will be thrown when there is a problem with the stream
	 * @throws GeneralSecurityException This exception will be thrown when there is a problem with the decryption
	 */
	public void getPublicKeyEncrypt(String password, OutputStream output)
		throws GeneralSecurityException, IOException
	{
		if (keyPair.getPublic() != null)
		{
			getKeyEncrypt(password, output, keyPair.getPublic());
		}
		else
		{
			throw new GeneralSecurityException("This key does not excist");
		}
	}
	/**
	 * Encrypt the private key with a password and returns the encypted key with the outputstream
	 * 
	 * @param password The password used for encryption
	 * @param output The encrypted key
	 * 
	 * @throws GeneralSecurityException This exception will be thrown when there is a problem getting the encrypted private key
	 * @throws IOException				This exception will be thrown when there is a problem with the stream
	 */
	public void getPrivateKeyEncrypt(String password, OutputStream output)
		throws GeneralSecurityException, IOException
	{
		if (keyPair.getPrivate() != null)
		{
			getKeyEncrypt(password, output, keyPair.getPrivate());
		}
		else
		{
			throw new GeneralSecurityException("This key does not excist");
		}
	}
	/**
	 * Encrypt a private key or public key with a password and returns the encypted key with the outputstream
	 * 
	 * @param password The password used for encryption
	 * @param output The encrypted key
	 * @param key The public or private key
	 * 
	 * @throws GeneralSecurityException This exception will be thrown when there is a getting the key
	 * @throws IOException				This exception will be thrown when there is a problem with the stream
	 */
	private void getKeyEncrypt(String password, OutputStream output, Key key)
		throws GeneralSecurityException, IOException
	{
		// create a secrate key with the password
		PBEParameterSpec paramSpec = new PBEParameterSpec(SALT, 20);
		PBEKeySpec keySpec = new PBEKeySpec(password.toCharArray());
		SecretKeyFactory kf =
			SecretKeyFactory.getInstance(KEY_ENCRIPTION_AKGORITHM);
		SecretKey passwordKey = kf.generateSecret(keySpec);
		// encrypt the key
		Cipher c = Cipher.getInstance(KEY_ENCRIPTION_AKGORITHM);
		c.init(Cipher.WRAP_MODE, passwordKey, paramSpec);
		byte[] wrappedKey = c.wrap(key);
		// write the key to the stream
		output.write(wrappedKey);
	}
}