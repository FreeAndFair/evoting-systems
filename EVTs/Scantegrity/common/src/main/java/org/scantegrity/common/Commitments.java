package org.scantegrity.common;

import javax.crypto.spec.SecretKeySpec;


/**
 * Computes salts and commitments for the P and D tables.
 * @author stefan
 *
 */
public class Commitments {
	
	public static byte[] P1CONSTANT="P1".getBytes();
	public static byte[] P2CONSTANT="P2".getBytes();
	
	public static byte[] CODECONSTANT="COD".getBytes();
	
	public static byte[] D1D2_HALF_ROW_CONSTANT="D12".getBytes();
	public static byte[] D4D5_HALF_ROW_CONSTANT="D54".getBytes();
	
	public static byte[] KEY_CONSTANT="KEY".getBytes();

	/** 
	 * @param salt
	 * @param c - public constant
	 * @param serial - the p id
	 * @param p1 - the message to be commitmed to
	 * @return a comitment to p1 computed using SecurityUtil.getCommitment 
	 * @throws Exception - no Exception is caugth and no Exception is Explicitly thrown 
	 */
	public static byte[] commitP(byte[] salt,byte[] c, byte[] serial,byte[] p1) throws Exception {
		return SecurityUtil.getCommitment(new SecretKeySpec(salt,"AES"),c,Util.makePMessage(serial, p1));
	}	

	public static byte[] commitCode(byte[] salt,byte[] c, byte[] id,byte[] code) throws Exception {
		return SecurityUtil.getCommitment(new SecretKeySpec(salt,"AES"),c,Util.makePMessage(id, code));
	}	

	
	/** 
	 * @param salt
	 * @param c - public constant
	 * @param partitionId
	 * @param instanceId
	 * @param rowId
	 * @param d1 - the pointer to P (or R)
	 * @param d2 - the transformation to be commited to
	 * @return a commitment to d2 using SecurityUtil.getCommitment 
	 * @throws Exception - no Exception is caugth and no Exception is Explicitly thrown
	 */
	public static byte[] commitD(byte[] salt,byte[] c, byte partitionId, byte instanceId, byte[] rowId,int d1,byte[] d2) throws Exception {
		return SecurityUtil.getCommitment(new SecretKeySpec(salt,"AES"),c,Util.makeDMessage(partitionId, instanceId, rowId, d1, d2));
	}

	/** 
	 * @param mk1
	 * @param mk2
	 * @param c
	 * @param serial
	 * @return the salt to be used for the p1 commitment
	 * @throws Exception - no Exception is caugth and no Exception is Explicitly thrown
	 */
	public static SecretKeySpec saltP1(SecretKeySpec mk1,SecretKeySpec mk2,byte[] c, byte[] serial) throws Exception {
		return saltP(mk1,mk2,c,serial,P1CONSTANT);
	}
	
	public static SecretKeySpec saltCode(SecretKeySpec mk1,SecretKeySpec mk2,byte[] c, byte[] serial) throws Exception {
		return saltP(mk1,mk2,c,serial,CODECONSTANT);
	}

	/** 
	 * @param mk1
	 * @param mk2
	 * @param c
	 * @param serial
	 * @return the salt to be used for the p2 commitment
	 * @throws Exception - no Exception is caugth and no Exception is Explicitly thrown
	 */
	public static SecretKeySpec saltP2(SecretKeySpec mk1,SecretKeySpec mk2,byte[] c, byte[] serial) throws Exception {
		return saltP(mk1,mk2,c,serial,P2CONSTANT);
	}	
	private static SecretKeySpec saltP(SecretKeySpec mk1,SecretKeySpec mk2,byte[] c, byte[] serial,byte[] constant) throws Exception {
		byte[] km=new byte[16];
		System.arraycopy(serial,0,km,0,serial.length);
		System.arraycopy(constant,0,km,serial.length,constant.length);
		return SecurityUtil.tripleAES(mk1,mk2,c,km);
	}
	
	/** 
	 * @param mk1
	 * @param mk2
	 * @param c
	 * @param partitionId
	 * @param dNo
	 * @param rowId
	 * @return the salt to be used for the commitment to the first half of a D row
	 * @throws Exception - no Exception is caugth and no Exception is Explicitly thrown
	 */
	public static SecretKeySpec saltDRowLeft(SecretKeySpec mk1,SecretKeySpec mk2,byte[] c, byte partitionId, byte dNo, byte[] rowId) throws Exception {
		return saltDRowHalf(mk1, mk2, c, partitionId, dNo, rowId, D1D2_HALF_ROW_CONSTANT);
	}
	/** 
	 * @param mk1
	 * @param mk2
	 * @param c
	 * @param partitionId
	 * @param dNo
	 * @param rowId
	 * @return - the salt to be used for the commitment to the second half of the D row
	 * @throws Exception - no Exception is caugth and no Exception is Explicitly thrown
	 */
	public static SecretKeySpec saltDRowRight(SecretKeySpec mk1,SecretKeySpec mk2,byte[] c, byte partitionId, byte dNo, byte[] rowId) throws Exception {
		return saltDRowHalf(mk1, mk2, c, partitionId, dNo, rowId, D4D5_HALF_ROW_CONSTANT);
	}
	
	private static SecretKeySpec saltDRowHalf(SecretKeySpec mk1,SecretKeySpec mk2,byte[] c, byte partitionId,byte dNo, byte[] rowId,byte[] constant) throws Exception {
		byte[] km=new byte[16];
		km[0]=partitionId;
		km[1]=dNo;
		int pos = 2;
		System.arraycopy(rowId,0,km,pos,rowId.length);
		pos+=rowId.length;
		System.arraycopy(constant,0,km,pos,D1D2_HALF_ROW_CONSTANT.length);
		return SecurityUtil.tripleAES(mk1,mk2,c,km);
	}
	
	public static SecretKeySpec KeyForCodeGeneration(SecretKeySpec mk1,SecretKeySpec mk2,byte[] c, byte[] serial,byte[] qno,byte[] constant) throws Exception {
		byte[] km=new byte[16];
		System.arraycopy(serial,0,km,0,serial.length);
		System.arraycopy(qno,0,km,serial.length+1,qno.length);
		System.arraycopy(constant,0,km,serial.length+1+qno.length+1,constant.length);
		return SecurityUtil.tripleAES(mk1,mk2,c,km);
	}

}
