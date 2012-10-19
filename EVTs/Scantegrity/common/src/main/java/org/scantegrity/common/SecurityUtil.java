package org.scantegrity.common;


import java.io.IOException;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.security.NoSuchProviderException;
import java.security.Security;
import java.security.cert.CertificateEncodingException;
import java.security.cert.X509Certificate;

import javax.crypto.Cipher;
import javax.crypto.NoSuchPaddingException;
import javax.crypto.spec.SecretKeySpec;

import org.bouncycastle.jce.provider.BouncyCastleProvider;
import org.bouncycastle.util.encoders.Base64;
import org.xml.sax.SAXException;

import org.scantegrity.common.Commitments;


public class SecurityUtil {

	public static Cipher cipherNoPaddingNoKey = null;
	public static Cipher cipherPkcs5Padding = null;
	
	/* maye improve performance by initializing the two chiphers with the master keys
	 * Or maybe not, cause it seems like doFinal calles init anyhow
	public static Cipher cipherNoPaddingMK1 = null;
	public static Cipher cipherNoPaddingMK2 = null;
	*/
	
	static MessageDigest sha = null;
	static {
		try {
			Security.addProvider(new BouncyCastleProvider());			
			cipherNoPaddingNoKey = Cipher.getInstance("AES/ECB/NoPadding");
			cipherPkcs5Padding = Cipher.getInstance("AES/ECB/PKCS5Padding");
			
			sha=MessageDigest.getInstance("SHA256","BC");
		} catch (NoSuchAlgorithmException e) {
			e.printStackTrace();
		} catch (NoSuchPaddingException e) {
			e.printStackTrace();
		} catch (NoSuchProviderException e) {
			e.printStackTrace();
		}		
	}

	
	/**
	 * generates a pseuso random AES 128bit key from "message".  
	 * The formula used to generate the key is: 
	 * Km = Dmk1 (C XOR Emk2 (C XOR Emk1(message))),
	 * where D standes for decrypt and E for Encrypt. Emk1 means Encrypt with the key "mk1"
	 * (master key 1). The encryption scheme used is AES/ECB/NoPadding
	 * the following restrictions apply:
	 * message.length = 16
	 * c.length = 16
	 * rawKey1.length = 16
	 * rawKey2.length = 16
	 * Otherwise the method will throw an Exception
	 * @param mk1 an AES 128 bit key 
	 * @param mk2 an AES 128 bit key
	 * @param c a constant. c.length = 16; 
	 * @param message 16byte message 
	 * @return an AES 128bit key
	 * @throws Exception - no exceptions are caugth
	 */	
	public static SecretKeySpec tripleAES(SecretKeySpec mk1,SecretKeySpec mk2,byte[] c,byte[] message) throws Exception {
		cipherNoPaddingNoKey.init(Cipher.ENCRYPT_MODE,mk1);
		byte[] emk1 = cipherNoPaddingNoKey.doFinal(message);
		cipherNoPaddingNoKey.init(Cipher.ENCRYPT_MODE,mk2);
		byte[] emk2 = cipherNoPaddingNoKey.doFinal(Util.xor(c,emk1));
		cipherNoPaddingNoKey.init(Cipher.DECRYPT_MODE,mk1);
		byte[] smkRaw = cipherNoPaddingNoKey.doFinal(Util.xor(c,emk2));
		return new SecretKeySpec(smkRaw,"AES");
	}
/*25percent improvment
	public static SecretKeySpec tripleAES(SecretKeySpec mk1,SecretKeySpec mk2,byte[] c,byte[] message) throws Exception {
		Mac mac = Mac.getInstance("HMACSHA256","BC");
		mac.init(mk1);
		return new SecretKeySpec(mac.doFinal(message),"AES");
	}
*/	
	
	/**
	 * Given a message m, a secretKey skm and a public constant 
	 * it returnes the commitment to the message m.
	 * The commitment is computed as follows:
	 * sak=Encrypt C with skm
	 * h1 = SHA256(m, sak).
	 * h2 = SHA256(m, Encrypt h1 with sak)
	 * the commitment is h1h2 (h1 concatenated with h2)
	 * where E stands for Encrypt.
	 * The encryption scheme used is AES/ECB/NoPadding
	 * 
	 * @param skm - the salt used in the commitment
	 * @param c - the public constant
	 * @param m - the message to be commited to
	 * @return - a commitment to m
	 * @throws Exception
	 */
	public static byte[] getCommitment(SecretKeySpec skm, byte[] c, byte[] m) throws Exception {
		boolean debug = false;
		if (debug) {
			System.out.print("m=");
			Util.print(m);
			System.out.println();
			
			System.out.print("C=");
			Util.print(c);
			System.out.println();
			
			System.out.print("skm=");
			Util.print(skm.getEncoded());
			System.out.println();
		}
		cipherNoPaddingNoKey.init(Cipher.ENCRYPT_MODE,skm);
		byte[] sak = cipherNoPaddingNoKey.doFinal(c);
		if (debug) {
			System.out.print("sak (C encrypted with skm)=");
			Util.print(sak);
			System.out.println();
		}
		//sha.reset();
		sha.update(m,0,m.length);
		sha.update(sak,0,sak.length);
		byte[] h1 = sha.digest();
		if (debug) {
			System.out.print("h1=");
			Util.print(h1);
			System.out.println();
		}
		
		SecretKeySpec sakSecretKey = new SecretKeySpec(sak,"AES");
		cipherNoPaddingNoKey.init(Cipher.ENCRYPT_MODE,sakSecretKey);
		byte[] h1c = cipherNoPaddingNoKey.doFinal(h1);
		if (debug) {
			System.out.print("h1 encrypted=");
			Util.print(h1c);
			System.out.println();
		}
		
		//sha.reset();
		sha.update(m,0,m.length);
		sha.update(h1c,0,h1c.length);
		byte[] h2 = sha.digest();
		if (debug) {
			System.out.print("h2 plain=");
			Util.print(h2);
			System.out.println();
		}
		byte[] ret = new byte[h1.length+h2.length];
		System.arraycopy(h1,0,ret,0,h1.length);
		System.arraycopy(h2,0,ret,h1.length,h2.length);
		
		if (debug) {
			System.out.print("h1 concatenated with h2=");
			Util.print(ret);
			System.out.println();
		}
		return ret;
	}
	
	/** 
	 * @param s1 - salt
	 * @param p1 - message
	 * @param c1 - commitment
	 * @param pid - p id
	 * @param c - public constant
	 * @throws SAXException if the commitment does not checks. 
	 * The commitment is constructed using SecurityUtil.getCommitment
	 */
	public static void checkProwCommitment(byte[] s1, byte[] p1, String c1, String pid,byte[] c) throws SAXException {
		byte[] c1Reconstructed=null;
		try {
			c1Reconstructed = SecurityUtil.getCommitment(new SecretKeySpec(s1,"AES"),c,Util.makePMessage((pid+"").getBytes(), p1));
		} catch (Exception e) {
			e.printStackTrace();
			throw new SAXException(e.getMessage());			
		}
		if ((new String(Base64.encode(c1Reconstructed))).compareTo(c1)!=0)
			throw new SAXException("P id="+pid+" doesn't check\n" +
					"p="+Util.toString(Base64.encode(p1))+"\n" +
							"s="+new String(Base64.encode(s1))+"\n" +
									"c="+c1);
	}	
	
	/** 
	 * @param s1 - salt
	 * @param d1 - d1 (pointer to P or R)
	 * @param d2 - transformation
	 * @param c1 - commitment
	 * @param partitionId
	 * @param dNo
	 * @param did
	 * @param c - public constant
	 * @throws SAXException if the commitment does not checks. 
	 * The commitment is constructed using SecurityUtil.getCommitment
	 */
	public static void checkDrowCommitment(byte[] s1,int d1,byte[] d2,String c1, byte partitionId, byte dNo, String did, byte[] c) throws SAXException {
		byte[] clReconstructed = null;
		try {
			clReconstructed = SecurityUtil.getCommitment(new SecretKeySpec(s1,"AES"),c,Util.makeDMessage(partitionId, dNo, (did+"").getBytes(), d1, d2));
		} catch (Exception e) {
			e.printStackTrace();
			throw new SAXException(e.getMessage());
		}

		if ((new String(Base64.encode(clReconstructed))).compareTo(c1)!=0)
			throw new SAXException("D id="+d1+" doesn't check\n" +
					"d="+Util.toString(Base64.encode(d2))+"\n" +
							"s="+new String(Base64.encode(s1))+"\n" +
									"c="+c1);	
	}
	
	public static void checkCodeCommitment(int serialPrinted, byte question, byte answer, byte[] salt, String code, byte[] comm,byte[] c) throws SAXException {
		byte[] c1Reconstructed=null;
		try {			
			c1Reconstructed=Commitments.commitCode(
					salt,
					c,
					new byte[0],
					(serialPrinted+" "+question+" "+answer+" "+code).getBytes());

		} catch (Exception e) {
			e.printStackTrace();
			throw new SAXException(e.getMessage());			
		}
		if (Util.compare(c1Reconstructed, comm)!=0) {
			try {
				Base64.encode(c1Reconstructed,System.out);
				System.out.println();
				Base64.encode(comm,System.out);
				System.out.println();
				System.out.flush();
			} catch (IOException e) {
				e.printStackTrace();
			}
			throw new SAXException("P serialPrinted="+serialPrinted+" doesn't check " +
					"q="+question +	" answer="+answer+" code="+code+"\n");
		}
//		System.out.println("commitment checked");
	}	

	
	public static void checkSerialsCommitment(BallotRow commitment, BallotRow salt, byte[] c) throws SAXException {
		byte[] reconstructedCommitment=null;

		//check the commitment for the chitSerialNumber
		try {
			reconstructedCommitment=Commitments.commitCode(
					salt.getWebSerialSalt(), 
					c,
					//(salt.getPid()+" "+salt.getWebSerial()).getBytes(),
					new byte[0],
					(salt.getPid()+" "+salt.getWebSerial()).getBytes());
		} catch (Exception e) {
			e.printStackTrace();
			throw new SAXException(e.getMessage());			
		}
		
		if (Util.compare(reconstructedCommitment, commitment.getWebSerialCommitment())!=0) {
			try {
				Base64.encode(reconstructedCommitment,System.out);
				System.out.println();
				Base64.encode(commitment.getWebSerialCommitment(),System.out);
				System.out.println();
				System.out.flush();
			} catch (IOException e) {
				e.printStackTrace();
			}
			throw new SAXException("The commitment to the "+BallotRow.webSerialAttr+" does not check "+BallotRow.barcodeSerialAttr+" "+salt.getBarcodeSerial()+"\n");
		}
		
		
		//check the commitment to password 1
		if (salt.getStubSerialSalt()!=null) {
			try {
				reconstructedCommitment=Commitments.commitCode(
						salt.getStubSerialSalt(), 
						c,
						//(salt.getPid()+" "+salt.getStubSerial()).getBytes(),
						new byte[0],
						(salt.getPid()+" "+salt.getStubSerial()).getBytes());
			} catch (Exception e) {
				e.printStackTrace();
				throw new SAXException(e.getMessage());			
			}
			
			if (Util.compare(reconstructedCommitment, commitment.getStubSerialCommitment())!=0) {
				try {
					Base64.encode(reconstructedCommitment,System.out);
					System.out.println();
					Base64.encode(commitment.getStubSerialCommitment(),System.out);
					System.out.println();
					System.out.flush();
				} catch (IOException e) {
					e.printStackTrace();
				}
				throw new SAXException("The commitment to the "+BallotRow.stubSerialAttr+" does not check for "+BallotRow.barcodeSerialAttr+" "+salt.getBarcodeSerial()+"\n");
			}
			//System.out.println("commitment to password1 checked");
		}
		/*
		//check the commitment to password2
		if (salt.getPassword2Salt()!=null) {
			try {
				reconstructedCommitment=Commitments.commitCode(
						salt.getPassword2Salt(), 
						c,(salt.getPid()+" "+salt.getPassword2()).getBytes(), (salt.getPid()+" "+salt.getPassword2()).getBytes());
			} catch (Exception e) {
				e.printStackTrace();
				throw new SAXException(e.getMessage());			
			}
			
			if (Util.compare(reconstructedCommitment, commitment.getPassword2Commitment())!=0) {
				try {
					Base64.encode(reconstructedCommitment,System.out);
					System.out.println();
					Base64.encode(commitment.getPassword2Commitment(),System.out);
					System.out.println();
					System.out.flush();
				} catch (IOException e) {
					e.printStackTrace();
				}
				throw new SAXException("The commitment to the "+BallotRow.password2Attr+" does not check for "+BallotRow.barcodeSerialAttr+" "+salt.getBarcodeSerial()+"\n");
			}
			//System.out.println("commitment to password2 checked");		
		}
		*/
	}	

	
	/**
	 * Converts an X509 certificate from BER to PEM 
	 * @param cert - an X509 Certificate
	 * @return - a String with the PEM format of the certificate(Base64, 65 characters per line)
	 * @throws CertificateEncodingException
	 */
	public static String toPEM(X509Certificate cert) throws CertificateEncodingException {
		StringBuffer ret=new StringBuffer();
		ret.append("-----BEGIN CERTIFICATE-----\n");
        byte[] certEncoded=Base64.encode(cert.getEncoded());
        int i=0;
        int len=0;
        while (i<certEncoded.length) {
        	len=Math.min(65, certEncoded.length-i);
        	ret.append(new String(certEncoded,i,len));
        	i+=len;
        	ret.append("\n");
        }
        ret.append("-----END CERTIFICATE-----\n");
    	return ret.toString();
	}
	
	public static void main(String args[]) throws Exception {
		String cs="PrincetonElectio";
		System.out.println("Constant String "+cs);
		String salt="dWvJjTDof3YHWyOYvkIFoA==";
		System.out.println("Salt Base64 "+salt);
		String ms="4 3 1 2 0 3 1 0 2 0 3 1 4 2 0 1";
		System.out.println("Message String "+ms);
		String pids="0";
		System.out.println("Pid String "+pids);
		System.out.println();
		
		SecretKeySpec skm=new SecretKeySpec(Base64.decode(salt),"AES");
		byte[] c=cs.getBytes();
		byte[] pid=pids.getBytes();
		byte[] p1=Util.parse(ms);
		byte[] m=Util.makePMessage(pid, p1);
		
		System.out.println("Commitment Base64="+new String(Base64.encode(getCommitment(skm, c, m))));
	}
}
