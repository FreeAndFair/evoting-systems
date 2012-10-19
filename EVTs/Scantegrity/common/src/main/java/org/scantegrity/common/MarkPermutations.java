package org.scantegrity.common;

import java.math.BigInteger;
import java.util.Collection;
import java.util.Iterator;
import java.util.TreeMap;
import java.util.Vector;

import javax.crypto.Cipher;
import javax.crypto.spec.SecretKeySpec;

import org.scantegrity.common.ballotstandards.basic.Question;
import org.scantegrity.common.ballotstandards.electionSpecification.ElectionSpecification;


/**
 * Computes the mark permutations using the following algorithm <BR>
 * For P:<BR>
 * Let M be a byte array of length 16 (see below how M is constructed for P1,P2,D2)
 * Compute a secret key SK = Dmk1(C xor Emk2(C xor Emk1(M))) AES128 ECB NoPadding
 * Let MM be a byte array of length 2, MM[0]=question number, MM[1]=answer number
 * Using the secret key SK, encrypt MM using AES128 ECB PKCS#5Padding
 * sort the cryptograms to generate the permutation
 * <BR>
 * For P1:<BR>
 * M=serial+"top"<BR>
 * For P2:<BR>
 * M=serial+"bottom"<BR>
 * For D2: <BR>
 * M=DInstanceNumber+serial+"d2"<BR>
 * 
 * D4 is computed from P1,P2,P4<BR>
 * 
 * The format of the permutatio is:<BR>
 * each permutation is represented as an array of possitive bytes (thus max 127).
 * The questions takes n possitions in the array (n is the number of answers)
 * , each possition having one element of the permutation. For example, if question 6 starts at possition 19
 * and has 4 answers, ans possitions 19,20,21 and 22 have 2,3,1,0 the permutation is 0->2,1->3,2->1,3->0 
 * @author Stefan
 *
 */
public class MarkPermutations {
	//master keys
	SecretKeySpec mk1=null,mk2=null;
	//election constant
	byte[] c=null;
	//how many answers a question has.
	byte[] noAnswersInAQuestion = null;
	//the cannonical form of the ballot
	byte[] nonFlipped = null;
	
	//constants to differentiate the permutation generation
	byte[] P1Constant = "P1".getBytes(); 
	byte[] P2Constant = "P2".getBytes();
	byte[] D2Constant = "D2".getBytes();
	
	private Vector<Integer> allQuestions;
	
	private int[] noAnswersInPartition;
	private int[] noAnswersUntilQuestion;
	private Vector<Vector<Integer>> partitions;
	
	private int[] maxNoAnswersInPartition;
	private int[] maxNoAnswersUntilQuestion;
	private byte[] maxNoAnswers;
	
	private int totalMaxNoAnswers;
	private int totalNoAnswers;
	
	Cipher cipher=null;
	/**
	 * 
	 * @param c - the public constant
	 * @param es - the Election Specification
	 * @param partitions - what questions are in each partition 
	 */
	public MarkPermutations(byte[] c,ElectionSpecification es, Vector<Vector<Integer>> partitions) {
		this.c = c;
		this.partitions=partitions;
		allQuestions=new Vector<Integer>();
		
		Question[] qs = es.getOrderedQuestions();
		noAnswersInAQuestion = new byte[qs.length];
		maxNoAnswers = new byte[qs.length];
		totalNoAnswers=0;
		for (int qno = 0; qno < qs.length; qno++) {
			noAnswersInAQuestion[qno] = (byte)qs[qno].getAnswers().size();
			totalNoAnswers+=noAnswersInAQuestion[qno];
			
			maxNoAnswers[qno]=(byte)qs[qno].getMax();

			allQuestions.add(qno);
		}
		
		noAnswersUntilQuestion=new int[qs.length];
		maxNoAnswersUntilQuestion= new int[qs.length];
		for (int qno = 1; qno < qs.length; qno++) {
			noAnswersUntilQuestion[qno]=noAnswersUntilQuestion[qno-1]+noAnswersInAQuestion[qno-1];
			maxNoAnswersUntilQuestion[qno]=maxNoAnswersUntilQuestion[qno-1]+maxNoAnswers[qno-1];
		}

		totalMaxNoAnswers=maxNoAnswersUntilQuestion[qs.length-1]+maxNoAnswers[qs.length-1];
		
		nonFlipped = new byte[totalNoAnswers];
		
		int l=0;
		for (int i=0;i<noAnswersInAQuestion.length;i++) {
			for (int j=0;j<noAnswersInAQuestion[i];j++) {
				nonFlipped[l++]=(byte)j;
			}
		}
		noAnswersInPartition=new int[partitions.size()];
		maxNoAnswersInPartition=new int[partitions.size()];
		for (int i=0;i<partitions.size();i++) {
			Vector<Integer> part=partitions.get(i);
			for (int j:part) {
				noAnswersInPartition[i]+=noAnswersInAQuestion[j];
				maxNoAnswersInPartition[i]+=maxNoAnswers[j];
			}
		}
		
		cipher = SecurityUtil.cipherPkcs5Padding;
	}


	/** 
	 * @param mk1 - master key 1
	 * @param mk2 - master key 2
	 * @param c - public constant
	 * @param es - Election Specification
	 * @param partitions - what questions are in each partition (ex {{0,1}{2}{3,4,5}} 
	 * means that there are 3 partitions, in the first one there are questions 0 and 1, in the 
	 * second one question 2 and in the third patition questions 3,4,5)
	 */
	public MarkPermutations(SecretKeySpec mk1,SecretKeySpec mk2,byte[] c,ElectionSpecification es, Vector<Vector<Integer>> partitions) {
		this(c,es,partitions);
		this.mk1 = mk1;
		this.mk2 = mk2;
	}
	
	/**
	 * @return a copy of the canonical form of the ballot (all the permutations
	 * are the identity permutatuion)
	 * @throws Exception - no Exception is caugth and no Exception is Explicitly thrown
	 */
	public byte[] getCanonical() {
		byte[] ret = new byte[nonFlipped.length];
		System.arraycopy(nonFlipped,0,ret,0,ret.length);
		return ret;
	}

	/**
	 * this permutation is pseudo-randomly generated
	 * @param serial the serial number of the ballot
	 * @return top permutation (for all partitions)
	 * @throws Exception - no Exception is caugth and no Exception is Explicitly thrown
	 */
	public byte[] getP1(byte[] serial) throws Exception {
		byte[] temp = new byte[16];
		System.arraycopy(serial,0,temp,0,serial.length);
		System.arraycopy(P1Constant,0,temp,serial.length,P1Constant.length);	
		return flip(temp,allQuestions,nonFlipped.length);
	}
	/**
	 * this permutation is pseudo-randomly generated
	 * @param serial the serial number of the ballot 
	 * @return the bottom permutation (for all partitions)
	 * @throws Exception
	 */
	public byte[] getP2(byte[] serial) throws Exception {
		byte[] temp = new byte[16];
		System.arraycopy(serial,0,temp,0,serial.length);
		System.arraycopy(P2Constant,0,temp,serial.length,P2Constant.length);		
		return flip(temp,allQuestions,nonFlipped.length);
	}

	/**
	 * this permutation is pseudo-randomly generated
	 * @param serial the serial number of the ballot 
	 * @param partitionId
	 * @return the top permutation for the questions in the given partitions
	 * @throws Exception - no Exception is caugth and no Exception is Explicitly thrown
	 */
	public byte[] getP1(byte[] serial,byte partitionId) throws Exception {
		byte[] temp = new byte[16];
		System.arraycopy(serial,0,temp,0,serial.length);
		System.arraycopy(P1Constant,0,temp,serial.length,P1Constant.length);		
		return flip(temp,partitions.get(partitionId), noAnswersInPartition[partitionId]);
	}
	/**
	 * this permutation is pseudo-randomly generated
	 * @param serial the serial number of the ballot 
	 * @param partitionId
	 * @return bottom permutation for the questions in the given partitions
	 * @throws Exception - no Exception is caugth and no Exception is Explicitly thrown
	 */
	public byte[] getP2(byte[] serial,byte partitionId) throws Exception {
		byte[] temp = new byte[16];
		System.arraycopy(serial,0,temp,0,serial.length);
		System.arraycopy(P2Constant,0,temp,serial.length,P2Constant.length);		
		return flip(temp,partitions.get(partitionId), noAnswersInPartition[partitionId]);
	}
	
	
	/**
	 * this permutation is pseudo-randomly generated
	 * @param dInstance the instance number of D
	 * @param did the serial number of the ballot
	 * @return the first permutation in D
	 * @throws Exception - no Exception is caugth and no Exception is Explicitly thrown
	 */
	public byte[] getD2(byte[] did,byte dInstance,int partitionId) throws Exception {
		byte[] temp = new byte[16];
		temp[0]=dInstance;;
		System.arraycopy(did,0,temp,1,did.length);
		System.arraycopy(D2Constant,0,temp,1 + did.length,D2Constant.length);		
		return flip(temp,partitions.get(partitionId), noAnswersInPartition[partitionId]);		
	}

	/** 
	 * @param d2 all the permutations for all partitions
	 * @return for each question, computes the inverse permutation. Returns a concatenation of them
	 * @throws Exception - no Exception is caugth and no Exception is Explicitly thrown
	 */
	public byte[] getInverseAllPartition(byte[] d2) throws Exception {
		if (d2.length!=totalNoAnswers)
			throw new Exception("d2.length="+d2.length+"!="+totalNoAnswers);
		byte[] d2i = new byte[d2.length];
		int l=0;
		int k;
		for (int partitionId=0;partitionId<partitions.size();partitionId++)
			for (int qno:partitions.get(partitionId)) {
				k=l;
				for (int j=0;j<noAnswersInAQuestion[qno];j++) {
					d2i[k+d2[l]] = (byte)j;
					l++;
				}
			}
		return d2i;
	}

	/** 
	 * @param d2 the permutations in a given partition
	 * @param partitionId - the partition id
	 * @return computes the inverse of each permutattion in the given partition
	 * @throws Exception - if the length of d2 is different then the length of the
	 * questions in the given partition, an Exception si thrown 
	 */
	public byte[] getInversePartition(byte[] d2,int partitionId) throws Exception {
		if (d2.length!=noAnswersInPartition[partitionId])
			throw new Exception("d2.length="+d2.length+"!="+noAnswersInPartition[partitionId]);
		
		byte[] d2i = new byte[d2.length];
		int l=0;
		int k;
		for (int qno:partitions.get(partitionId)) {
			k=l;
			for (byte j=0;j<noAnswersInAQuestion[qno];j++) {
				d2i[k+d2[l]] = j;
				l++;
			}
		}
		return d2i;
	}	
	
	/**
	 * permutation is deterministically generated. 
	 * @param top the top permutation
	 * @param bottom the bottom permutation
	 * @param d2 the first permutation in D
	 * @return the second permutation in D = flip1-1 o bottom o top-1	
	 * @throws Exception - no Exception is caugth and no Exception is Explicitly thrown 
	 */
	public byte[] getD4(byte[] top,byte[] bottom,byte[] d2,byte partitionId) throws Exception {
		//compute d2Inverse
		byte[] d2i=getInversePartition(d2, partitionId);
		if (top.length>d2.length) {
			//project top on the current partition
			top = project(top, partitionId);
		}
		
		byte[] topi = getInversePartition(top, partitionId);
		
		if (bottom.length>d2.length) {
			//project bottom on the current partition
			bottom = project(bottom, partitionId);
		}
		
		byte[] d4 = new byte[noAnswersInPartition[partitionId]];		
		int l=0;
		for (int i:partitions.get(partitionId)) {
			for (int j=0;j<noAnswersInAQuestion[i];j++) {
				d4[l+j] = topi[l+bottom[l+d2i[l+j]]];
			}
			l+=noAnswersInAQuestion[i];
		}
		return d4;
	}

	/**
	 * Projects a byte array on a given partition I.E extracts only the
	 * possitions that corespond to the given partition from the byte array
	 * and concatenates them together 
	 * @param p - the permutation for all the questions
	 * @param partitionId
	 * @return - the permutatuions for the given partition
	 */
	public byte[] project(byte[] p, int partitionId) {
		byte[] ret=new byte[noAnswersInPartition[partitionId]];
		int retPos=0;
		for (int i:partitions.get(partitionId)) {
			System.arraycopy(p, noAnswersUntilQuestion[i], ret, retPos, noAnswersInAQuestion[i]);
			retPos+=noAnswersInAQuestion[i];
		}
		return ret;
	}
	
	/**
	 * Let keyMaterial be some key SK
	 * Let MM be a byte array of length 2, MM[0]=question number, MM[1]=answer number
	 * Using the secret key SK, encrypt MM using AES128 ECB PKCS#5Padding
	 * sort the cryptograms to generate the permutation 
	 * @param keyMatterial - the key that encrypts MM 
	 * @param qIds - the questions show answers are going to be permuted
	 * @param totalNoAnswers - the sum of the number of answers for all given questions (needed for performance reasons)
	 * @return a pseudo-randomly generated permutation
	 * @throws Exception - no Exception is caugth and no Exception is Explicitly thrown 
	 */
	private byte[] flip(byte[] keyMatterial, Vector<Integer> qIds,int totalNoAnswers) throws Exception {
		byte[] ret = new byte[totalNoAnswers];
		int retPos = 0;
		byte[] enc = null;
		byte[] temp = new byte[2];
		TreeMap<BigInteger,Byte> encAns = null;
	
		//compute the key for this flip
		SecretKeySpec skm = SecurityUtil.tripleAES(mk1,mk2,c,keyMatterial);

		cipher.init(Cipher.ENCRYPT_MODE,skm);
		//for every question
		for (int i:qIds) {
			temp[0] = (byte)i;
			encAns = new TreeMap<BigInteger,Byte>();
			for (byte j=0;j<noAnswersInAQuestion[i];j++) {
				temp[1] = j;
				enc = cipher.doFinal(temp);
				encAns.put(new BigInteger(enc),j);
			}
			//sort the cryptograms of the answers, thus generating a pseudo random permutation
			Collection<Byte> values = encAns.values();
			for(Iterator<Byte> v=values.iterator();v.hasNext();) {
				ret[retPos++]=v.next();
			}						
		}		
		return ret;
	}
	
	/**
	 * @return the total number of answers (in all the questions)
	 */
	public int getSize() {
		return nonFlipped.length;
	}

	/** 
	 * @param q - question number
	 * @return - the total number of answers in question q
	 */
	private int getNoAnswersInQuestion(int q) {
		return noAnswersInAQuestion[q];
	}
		
	/** 
	 * @param partitionId
	 * @return the total number of answers for questions in the given partition
	 */
	public int getNoAnswersInPartition(int partitionId) {
		return noAnswersInPartition[partitionId];
	}

	/** 
	 * @param q - question numbers
	 * @return - the maximum number of answers that a voter can select for a particular question
	 */
	public int getMaxNoAnswersInQuestion(int q) {
		return maxNoAnswers[q];
	}
	
	private int getMaxNoAnswersUntilQuestion(int q) {
		return maxNoAnswersUntilQuestion[q];
	}
	
	/** 
	 * @param partitionId
	 * @return - the maximum number of answers that a voter can select for the question in a given partition (their sum)
	 */
	public int getMaxNoAnswersInPartition(int partitionId) {
		return maxNoAnswersInPartition[partitionId];
	}
	
	/**
	 * Composes two layers. For each question, composes the permutations. 
	 * @param p1 - the permutation that is appleid second 
	 * @param p2 - the permutation that is applied first
	 * @return p1[p2]
	 */
	public byte[] compose(byte[] p1, byte[] p2) {
		if (p1==null || p2==null)
			return null;
		byte[] ret=new byte[p1.length];
		int k=0;
		for (int qno:allQuestions) {
			for (int a=0;a<noAnswersInAQuestion[qno];a++) {
				ret[k+a]=p1[k+p2[k+a]];
			}
			k+=noAnswersInAQuestion[qno];
		}
		return ret;
	}

	/** 
	 * Composes two layers. For each question in the given partition, composes the permutations.
	 * @param p1 - the permutation that is appleid second 
	 * @param p2 - the permutation that is applied first
	 * @param partitionId
	 * @return p1[p2]
	 */
	public byte[] compose(byte[] p1, byte[] p2, byte partitionId) {		
		byte[] ret=new byte[noAnswersInPartition[partitionId]];
		int k=0;
		for (int qno:partitions.get(partitionId)) {
			for (int a=0;a<noAnswersInAQuestion[qno];a++) {
				ret[k+a]=p2[k+p1[k+a]];
			}
			k+=noAnswersInAQuestion[qno];
		}
		return ret;	
	}

	/** 
	 * @return the total number of answers that the voter can select (for the entire ballot)
	 */
	public int getTotalMaxNoAnswers() {
		return totalMaxNoAnswers;
	}
	
	/** 
	 * @return the total number of answers on the ballot
	 */
	public int getTotalNoAnswers() {
		return totalNoAnswers;
	}
	
	/**
	 * @param p3 - the selection made by the voter (the entire selection, not just for the given partition)
	 * @param d2 - the transformation
	 * @param partitionId
	 * @return - extracts the selection made by the voter for the given partition and applies the d2 transformation to the selection in each question
	 * @throws Exception if p3.length!=total number of answers that the voter can select on the entire ballot (non votes are represented by -1)
	 * or if d2.length!=the number of answers in the given partition (the sum for all the questions)
	 */
	public byte[] computeD3(byte[] p3, byte[] d2, byte partitionId) throws Exception {		
		if (p3.length!=getTotalMaxNoAnswers())
			throw new Exception("p3.length="+p3.length+"!="+getTotalMaxNoAnswers()+". No not project P3");

		if (d2.length!=getNoAnswersInPartition(partitionId))
			throw new Exception("d2.length="+d2.length+"!="+getNoAnswersInPartition(partitionId)+". Project D2 on the partition "+partitionId);
			
		byte[] d3=new byte[getMaxNoAnswersInPartition(partitionId)];
		
		int p3Pos=0;
		int d2Pos=0;
		int d3Pos=0;
		for (int q:partitions.get(partitionId)) {
			p3Pos=getMaxNoAnswersUntilQuestion(q);
			for (int a=0;a<getMaxNoAnswersInQuestion(q);a++) {
				if (p3[p3Pos+a]==-1)
					d3[d3Pos+a]=-1;
				else {
					if (p3[p3Pos+a]<-1 || p3[p3Pos+a]>=noAnswersInAQuestion[q]) {
						System.out.print("Invalid vote in p3 for question "+q+" a="+a+" p3=");
						Util.print(p3);
						System.out.println(" Treating it as -1");
						
						d3[d3Pos+a]=-1;
					} else
						d3[d3Pos+a] = d2[d2Pos+p3[p3Pos+a]];
				}
			}
			d2Pos+=getNoAnswersInQuestion(q);			
			d3Pos+=getMaxNoAnswersInQuestion(q);
		}
		return d3;
	}
	/** 
	 * @param d3 - the partial decripted balot in the D table
	 * @param d4 - the second transformation in the D table
	 * @param partitionId
	 * @return - applies the d4 transformation to d3
	 * @throws Exception if d3.length!=the maximum number of answers the voter can select for the questions in the given partition (their sum)
	 * or if d4.length!=the total number of answers in the given partition (the sum for all the questions)
	 */
	public byte[] computeR(byte[] d3, byte[] d4, byte partitionId) throws Exception {
		if (d3.length!=getMaxNoAnswersInPartition(partitionId))
			throw new Exception("d3.length="+d3.length+"!="+getMaxNoAnswersInPartition(partitionId));

		if (d4.length!=getNoAnswersInPartition(partitionId))
			throw new Exception("d4.length="+d4.length+"!="+getNoAnswersInPartition(partitionId));
			
		byte[] r=new byte[getMaxNoAnswersInPartition(partitionId)];
		
		int d3Pos=0;
		int d4Pos=0;
		int rPos=0;
		for (int q:partitions.get(partitionId)) {
			for (int a=0;a<getMaxNoAnswersInQuestion(q);a++) {
				if (d3[d3Pos+a]==-1)
					r[rPos+a]=-1;
				else {
					if (d3[d3Pos+a]<-1 || d3[d3Pos+a]>=noAnswersInAQuestion[q]) {
						System.out.print("Invalid vote in d3 for question "+q+" d3=");
						Util.print(d3);
						System.out.println(" Treating it as -1");
						
						r[rPos+a]=-1;
					} else
						r[rPos+a] = d4[d4Pos+d3[d3Pos+a]];
				}
			}
			d3Pos+=getMaxNoAnswersInQuestion(q);
			d4Pos+=getNoAnswersInQuestion(q);			
			rPos+=getMaxNoAnswersInQuestion(q);
		}
		return r;
	}
	
}