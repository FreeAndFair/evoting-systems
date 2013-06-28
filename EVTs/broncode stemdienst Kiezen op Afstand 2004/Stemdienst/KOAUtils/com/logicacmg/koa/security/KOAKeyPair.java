/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.security.KOAKeyPair.java
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
  *  0.1		01-05-2003	MKu			First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.security;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.security.InvalidAlgorithmParameterException;
import java.security.InvalidKeyException;
import java.security.Key;
import java.security.KeyPair;
import java.security.KeyPairGenerator;
import java.security.NoSuchAlgorithmException;
import java.security.PrivateKey;
import java.security.PublicKey;
import java.security.spec.InvalidKeySpecException;

import javax.crypto.Cipher;
import javax.crypto.IllegalBlockSizeException;
import javax.crypto.NoSuchPaddingException;
import javax.crypto.SecretKey;
import javax.crypto.SecretKeyFactory;
import javax.crypto.spec.PBEKeySpec;
import javax.crypto.spec.PBEParameterSpec;

import com.logicacmg.koa.constants.ErrorConstants;
import com.logicacmg.koa.constants.TechnicalProps;
import com.logicacmg.koa.exception.KOAException;
import com.logicacmg.koa.utils.KOALogHelper;
/**
 * The KOA key pair is a class to generate the key pair.
 * This is a public and a private key.
 * 
 * It can also be used to decrypt a key with a password.
 * 
 * @author KuijerM
 */
public class KOAKeyPair
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
	 * @throws KOAException This exception will be thrown when there is a problem with generation a key pair
	 */
	public KOAKeyPair() throws KOAException
	{
		try
		{
			KEYPAIR_KEY_LENGTH =
				TechnicalProps.getIntProperty(TechnicalProps.RSA_KEY_LENGTH);
			KeyPairGenerator keyPairGen =
				KeyPairGenerator.getInstance(KEYPAIR_GENERATOR_ALGORITHM);
			keyPairGen.initialize(KEYPAIR_KEY_LENGTH);
			keyPair = keyPairGen.generateKeyPair();
		}
		catch (NoSuchAlgorithmException nsae)
		{
			//KOALogHelper.logError ("KOAKeyPair", "Cannot generate key pair", nsae);
			throw new KOAException(
				ErrorConstants.SECURITY_KEYPAIR_GENERATE,
				nsae);
		}
	}
	/** 
	 * Constructor for decryption of a key. 
	 * Only the public of private key of the <code>keyType</code> will be available the other will return null
	 * 
	 * @param password The password used for decryption
	 * @param criptKey A stream with the encrypted key
	 * @param keyType The type of the key public (<code>PUBLIC_KEY</code>) or private (<code>PRIVATE_KEY</code>)
	 * 
	 * @throws KOAException This exception will be thrown when there is a problem with decryption
	 */
	public KOAKeyPair(String password, InputStream cryptKey, int keyType)
		throws KOAException
	{
		try
		{
			KEYPAIR_KEY_LENGTH =
				TechnicalProps.getIntProperty(TechnicalProps.RSA_KEY_LENGTH);
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
		catch (NoSuchAlgorithmException nsae)
		{
			KOALogHelper.logError(
				"KOAKeyPair",
				"Cannot decrypt key pair",
				nsae);
			throw new KOAException(
				ErrorConstants.SECURITY_KEYPAIR_DECRYPT,
				nsae);
		}
		catch (NoSuchPaddingException nspe)
		{
			KOALogHelper.logError(
				"KOAKeyPair",
				"Cannot decrypt key pair",
				nspe);
			throw new KOAException(
				ErrorConstants.SECURITY_KEYPAIR_DECRYPT,
				nspe);
		}
		catch (InvalidKeySpecException ikse)
		{
			KOALogHelper.logError(
				"KOAKeyPair",
				"Cannot decrypt key pair",
				ikse);
			throw new KOAException(
				ErrorConstants.SECURITY_KEYPAIR_DECRYPT,
				ikse);
		}
		catch (InvalidKeyException ike)
		{
			KOALogHelper.logError("KOAKeyPair", "Cannot decrypt key pair", ike);
			throw new KOAException(
				ErrorConstants.SECURITY_KEYPAIR_DECRYPT,
				ike);
		}
		catch (InvalidAlgorithmParameterException iape)
		{
			KOALogHelper.logError(
				"KOAKeyPair",
				"Cannot decrypt key pair",
				iape);
			throw new KOAException(
				ErrorConstants.SECURITY_KEYPAIR_DECRYPT,
				iape);
		}
		catch (IOException ioe)
		{
			KOALogHelper.logError("KOAKeyPair", "Cannot decrypt key pair", ioe);
			throw new KOAException(
				ErrorConstants.SECURITY_KEYPAIR_DECRYPT,
				ioe);
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
	 * @throws IOException This exception will be thrown when there is a problem with the stream
	 * @throws KOAException This exception will be thrown when there is a problem with the decription
	 */
	public void getPublicKeyEncrypt(String password, OutputStream output)
		throws KOAException
	{
		if (keyPair.getPublic() != null)
		{
			getKeyEncrypt(password, output, keyPair.getPublic());
		}
		else
		{
			throw new KOAException(
				ErrorConstants.SECURITY_KEYPAIR_ENCRYPT_PUBLIC);
		}
	}
	/**
	 * Encrypted the private key with a password and returns the encypted key with the outputstream
	 * 
	 * @param password The password used for encryption
	 * @param output The encrypted key
	 * @throws KOAException This exception will be thrown when there is a problem getting the encrypted private key
	 */
	public void getPrivateKeyEncrypt(String password, OutputStream output)
		throws KOAException
	{
		if (keyPair.getPrivate() != null)
		{
			getKeyEncrypt(password, output, keyPair.getPrivate());
		}
		else
		{
			throw new KOAException(
				ErrorConstants.SECURITY_KEYPAIR_ENCRYPT_PRIVATE);
		}
	}
	/**
	 * Encrypted a private key or public key with a password and returns the encypted key with the outputstream
	 * 
	 * @param password The password used for encryption
	 * @param output The encrypted key
	 * @param key The public or private key
	 * @throws KOAException This exception will be thrown when there is a getting the key
	 */
	private void getKeyEncrypt(String password, OutputStream output, Key key)
		throws KOAException
	{
		try
		{
			// create a secret key with the password
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
		catch (NoSuchAlgorithmException nsae)
		{
			KOALogHelper.logError(
				"KOAKeyPair.getKeyEncrypt",
				"Problem encrypting key",
				nsae);
			throw new KOAException(
				ErrorConstants.SECURITY_KEYPAIR_ENCRYPT,
				nsae);
		}
		catch (NoSuchPaddingException nspe)
		{
			KOALogHelper.logError(
				"KOAKeyPair.getKeyEncrypt",
				"Problem encrypting key",
				nspe);
			throw new KOAException(
				ErrorConstants.SECURITY_KEYPAIR_ENCRYPT,
				nspe);
		}
		catch (IllegalBlockSizeException iape)
		{
			KOALogHelper.logError(
				"KOAKeyPair.getKeyEncrypt",
				"Problem encrypting key",
				iape);
			throw new KOAException(
				ErrorConstants.SECURITY_KEYPAIR_ENCRYPT,
				iape);
		}
		catch (InvalidKeySpecException ikse)
		{
			KOALogHelper.logError(
				"KOAKeyPair.getKeyEncrypt",
				"Problem encrypting key",
				ikse);
			throw new KOAException(
				ErrorConstants.SECURITY_KEYPAIR_ENCRYPT,
				ikse);
		}
		catch (InvalidKeyException ike)
		{
			KOALogHelper.logError(
				"KOAKeyPair.getKeyEncrypt",
				"Problem encrypting key",
				ike);
			throw new KOAException(
				ErrorConstants.SECURITY_KEYPAIR_ENCRYPT,
				ike);
		}
		catch (InvalidAlgorithmParameterException iape)
		{
			KOALogHelper.logError(
				"KOAKeyPair.getKeyEncrypt",
				"Problem encrypting key",
				iape);
			throw new KOAException(
				ErrorConstants.SECURITY_KEYPAIR_ENCRYPT,
				iape);
		}
		catch (IOException ioe)
		{
			KOALogHelper.logError(
				"KOAKeyPair.getKeyEncrypt",
				"Problem encrypting key",
				ioe);
			throw new KOAException(
				ErrorConstants.SECURITY_KEYPAIR_ENCRYPT,
				ioe);
		}
	}
	public static void main(String[] args)
	{
		java.security.Security.addProvider(
			new com.sun.crypto.provider.SunJCE());
		java.security.Security.addProvider(new com.sun.rsajca.Provider());
		try
		{
			java.io.FileOutputStream fosPub =
				new java.io.FileOutputStream("d:\\temp\\publickey.pk");
			java.io.FileOutputStream fosPriv =
				new java.io.FileOutputStream("d:\\temp\\privatekey.pk");
			//ByteArrayOutputStream os = new ByteArrayOutputStream ();
			System.out.println("Got outputstream");
			KOAKeyPair pair = new KOAKeyPair();
			System.out.println("created new koakeypair");
			pair.getPrivateKeyEncrypt("koa", fosPriv);
			pair.getPublicKeyEncrypt("koa", fosPub);
			fosPriv.close();
			fosPub.close();
			System.out.println("created public and private key");
		}
		catch (Exception e)
		{
			System.err.println("Error in main");
			e.printStackTrace();
		}
	}
}