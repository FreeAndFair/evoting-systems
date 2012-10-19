package org.scantegrity.common;

import java.math.BigInteger;
import java.util.Collection;
import java.util.Iterator;
import java.util.TreeMap;

import javax.crypto.Cipher;
import javax.crypto.spec.SecretKeySpec;


/**
 * Computes the row permutations using the following algorithm <BR>
 * Let M be a byte array of length 16. On the first possitions M will have tableInstance.
 * On the following possitions M will have columnName
 * Compute a secret key SK = Dmk1(C xor Emk2(C xor Emk1(M))) AES128 ECB NoPadding
 * Let MM be a byte array with the string representation of the serial numbers
 * Using the secret key SK, encrypt MM using AES128 ECB PKCS#5Padding
 *  - sort the cryptograms to generate the permutation
*/
public class RowPermutation {
	public static byte[] D1D5CONSTANT = "D1D5".getBytes();
	public static byte[] D1CONSTANT = "D1".getBytes();
	
	public static byte[] BARCODESERIAL = "BARCODESERIAL".getBytes();
	public static byte[] SERIALONCHITS = "SERIALONCHITS".getBytes();
	public static byte[] PASSWORD1ONCHITS = "PASSWORD1ONCHITS".getBytes();
	public static byte[] PASSWORD2ONCHITS = "PASSWORD2ONCHITS".getBytes();
	
	/**
	 * Gets the permutation mapping D1 to D5. This maping is the same for 
	 * all the instances of the D tables (because one P has to be mapped to one R)
	 * 
	 * @param mk1 - master key 1
	 * @param mk2 - master key 2
	 * @param c - public constant
	 * @param startSerial - the first serial numbered considered (ussualy 0) 
	 * @param endSerial - the last serial number considered (including) (ussualy the number of ballots)
	 * @param partitionId
	 * @return a permutation of length endSerial-startSerial+1
	 * @throws Exception - no Exception is caugth and no Exception is Explicitly thrown 
	 */
	public static int[] permuteD1D5(SecretKeySpec mk1,SecretKeySpec mk2,byte[] c,int startSerial,int endSerial, byte partitionId) throws Exception {
		byte[] skmRaw = new byte[16];
		System.arraycopy(D1D5CONSTANT,0,skmRaw,0,D1D5CONSTANT.length);
		skmRaw[D1D5CONSTANT.length]=partitionId;
		return RowPermutation.permute(mk1,mk2,c,skmRaw,startSerial,endSerial);
	}

	/**
	 * Gets the permutation mapping D to P. This permutation is different for
	 * every instance of the D table
	 * @param mk1 - master key 1
	 * @param mk2 - master key 2
	 * @param c - public constant
	 * @param tableInstance
	 * @param startSerial - the first serial numbered considered (ussualy 0) 
	 * @param endSerial - the last serial number considered (including) (ussualy the number of ballots)
	 * @param partitionId
	 * @return a permutation of length endSerial-startSerial+1
	 * @throws Exception - no Exception is caugth and no Exception is Explicitly thrown 
	 */
	public static int[] permuteD1(SecretKeySpec mk1,SecretKeySpec mk2,byte[] c,byte tableInstance,int startSerial,int endSerial,byte partitionId) throws Exception {
		byte[] skmRaw = new byte[16];
		System.arraycopy(D1CONSTANT,0,skmRaw,0,D1CONSTANT.length);
		skmRaw[D1CONSTANT.length]=tableInstance;
		skmRaw[D1CONSTANT.length+1]=partitionId;
		return RowPermutation.permute(mk1,mk2,c,skmRaw,startSerial,endSerial);
	}

	public static String[] generateBarcodeSerialNumbers(SecretKeySpec mk1,SecretKeySpec mk2,byte[] c, String prefix, int startRange,int endRange, int size) throws Exception {
		byte[] skmRaw = new byte[16];
		System.arraycopy(BARCODESERIAL,0,skmRaw,0,BARCODESERIAL.length);
		int[] temp = RowPermutation.permute(mk1,mk2,c,skmRaw,startRange,endRange);
		String[] ret = new String[size];		
		for (int i=0;i<ret.length;i++) {
			ret[i]=prefix+temp[i];
		}
		return ret;
	}
	
	public static String[] generateWebSerials(SecretKeySpec mk1,SecretKeySpec mk2,byte[] c, String prefix, int startRange,int endRange, int size) throws Exception {
		byte[] skmRaw = new byte[16];
		System.arraycopy(SERIALONCHITS,0,skmRaw,0,SERIALONCHITS.length);
		int[] temp = RowPermutation.permute(mk1,mk2,c,skmRaw,startRange,endRange);
		String[] ret = new String[size];
		
		for (int i=0;i<ret.length;i++) {
			ret[i]=prefix+temp[i];
		}
 
		return ret;
	}

	public static String[] generateStubSerials(String prefix,int startRange, int size) throws Exception {
		String[] ret = new String[size];
		for (int i=0;i<ret.length;i++) {
			ret[i]=prefix+Util.AddleadingZeros((startRange+i)+"",4);
		}
		return ret;
	}
/*
	public static int[] generatePassword2(SecretKeySpec mk1,SecretKeySpec mk2,byte[] c,int startRange,int endRange, int size) throws Exception {
		byte[] skmRaw = new byte[16];
		System.arraycopy(PASSWORD2ONCHITS,0,skmRaw,0,PASSWORD2ONCHITS.length);
		int[] temp = RowPermutation.permute(mk1,mk2,c,skmRaw,startRange,endRange);
		int[] ret = new int[size];
		System.arraycopy(temp,0,ret,0,ret.length);
		return ret;
	}
*/
	
	/**
	 * Deterministically computes the mapping between D and R, based on the mapping between
	 * P and D (D1) and D1 to D5. 
	 * @param master the D1D5 permutation
	 * @param d1 d1 permutation
	 * @return master[d1]
	 * @throws Exception - no Exception is caugth and no Exception is Explicitly thrown 
	 */
	public static int[] permuteD5(int[] master,int[] d1) throws Exception {
	 int[] ret = new int[master.length];
		for (int i=0;i<ret.length;i++) {
			ret[i] = master[d1[i]];
		}
	return ret;
	}
	
	/**
	 * Computes the row permutations using the following algorithm <BR>
	 * Let M be a byte array of length 16. On the first possitions M will have tableInstance.
	 * On the following possitions M will have columnName
	 * Compute a secret key SK = Dmk1(C xor Emk2(C xor Emk1(M))) AES128 ECB NoPadding
	 * Let MM be a byte array with the string representation of the serial numbers
	 * Using the secret key SK, encrypt MM using AES128 ECB PKCS#5Padding
	 *  - sort the cryptograms to generate the permutation
	 * <BR> 
	 * @param rawKey1 master key 1
	 * @param rawKey2 master key 2
	 * @param c public constant
	 * @param tableInstance the instance od D as a byte array
	 * @param columnName the column name of D as a byte array
	 * @param startSerial
	 * @param endSerial
	 * @return a permutation with elements starting at startSerial ending at endSerial
	 * @throws Exceptionno new Exceptions are thrown
	 */
	private static int[] permute(SecretKeySpec mk1,SecretKeySpec mk2,byte[] c,byte[] smkRaw,int startSerial,int endSerial) throws Exception {
		SecretKeySpec skm = SecurityUtil.tripleAES(mk1,mk2,c,smkRaw);
		
		int[] perm = new int[endSerial-startSerial+1];
		TreeMap<BigInteger,Integer> permuted = new TreeMap<BigInteger,Integer>();
		Cipher cipher = SecurityUtil.cipherPkcs5Padding;
		cipher.init(Cipher.ENCRYPT_MODE,skm);
		for (int i=startSerial;i<startSerial+perm.length;i++) {
			byte[] enc = cipher.doFinal((""+i).getBytes());		
			permuted.put(new BigInteger(enc),i);
		}
		//sorting is done automatically
		Collection<Integer> permVal = permuted.values();
		int j=0;
		for (Iterator<Integer> i=permVal.iterator();i.hasNext();) {
			perm[j++] = i.next();
		}
		return perm;
	}
}
