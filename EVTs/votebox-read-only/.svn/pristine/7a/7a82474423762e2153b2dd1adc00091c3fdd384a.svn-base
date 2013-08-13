package edu.uconn.cse.adder;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.NoSuchElementException;
import java.util.StringTokenizer;

import sexpression.ASExpression;
import sexpression.ListExpression;
import sexpression.StringExpression;

/**
 * Represents a membership proof.
 *
 * @author David Walluck
 * @version $LastChangedRevision$ $LastChangedDate$
 * @since 0.0.1
 */
public class MembershipProof {
	private AdderInteger p;
	private AdderInteger q;
	private AdderInteger c;
	private List<AdderInteger> yList;
	private List<AdderInteger> zList;
	private List<AdderInteger> sList;
	private List<AdderInteger> cList;

	/**
	 * Constructs a new <code>MembershipProof</code> object with the specified
	 * prime.
	 */
	public MembershipProof() {
		yList = new ArrayList<AdderInteger>();
		zList = new ArrayList<AdderInteger>();
		sList = new ArrayList<AdderInteger>();
		cList = new ArrayList<AdderInteger>();
	}

	/**
	 * Constructs a new <code>MembershipProof</code> object with the specified
	 * prime.
	 *
	 * @param p the prime
	 * @param q the sub-prime
	 * @param yList the y list
	 * @param zList the z list
	 * @param sList the s list
	 * @param cList the c list
	 */
	private MembershipProof(AdderInteger p, AdderInteger q,
			List<AdderInteger> yList,
			List<AdderInteger> zList,
			List<AdderInteger> sList,
			List<AdderInteger> cList) {
		this.p = p;
		this.q = q;
		this.yList = yList;
		this.zList = zList;
		this.sList = sList;
		this.cList = cList;
	}

	/**
	 * Computes the actual proof given the ciphertext, public key, value,
	 * and domain.
	 *
	 * @param ciphertext the ciphertext
	 * @param pubKey the public key
	 * @param value the value
	 * @param domain the domain
	 */
	public void compute(ElgamalCiphertext ciphertext, PublicKey pubKey,
			AdderInteger value,
			List/*<AdderInteger>*/ domain) {
		this.p = pubKey.getP();
		this.q = pubKey.getQ();

		AdderInteger g = new AdderInteger(pubKey.getG(), this.p);
		AdderInteger h = pubKey.getH();
		AdderInteger f = pubKey.getF();

		AdderInteger bigG = ciphertext.getG();
		AdderInteger bigH = ciphertext.getH();
		AdderInteger r = ciphertext.getR();

		AdderInteger t = AdderInteger.random(q);

		StringBuffer sb = new StringBuffer(4096);

		sb.append(g);
		sb.append(h);
		sb.append(bigG);
		sb.append(bigH);

		int indexInDomain = 0;

		for (int i = 0; i < domain.size(); i++) {
			AdderInteger y;
			AdderInteger z;
			AdderInteger d = (AdderInteger) domain.get(i);

			if (d.equals(value)) {
				sList.add(AdderInteger.ZERO);
				cList.add(AdderInteger.ZERO);
				y = g.pow(t);
				z = h.pow(t);
				indexInDomain = i;
			} else {
				sList.add(AdderInteger.random(q));
				cList.add(AdderInteger.random(q));
				AdderInteger s = (AdderInteger) sList.get(i);
				AdderInteger c = (AdderInteger) cList.get(i);
				AdderInteger negC = c.negate();
				AdderInteger fpow = f.pow(d);
				y = g.pow(s).multiply(bigG.pow(negC));
				z = h.pow(s).multiply(bigH.divide(fpow).pow(negC));
			}

			yList.add(y);
			zList.add(z);

			sb.append(y);
			sb.append(z);
		}

		String s = sb.toString();
		String cHash = Util.sha1(s);

		this.c = new AdderInteger(cHash, q, 16).mod(q);
		AdderInteger realC = new AdderInteger(this.c, q);

		for (int i = 0; i < cList.size(); i++) {
			AdderInteger fakeC = (AdderInteger) cList.get(i);
			realC = realC.subtract(fakeC);
		}

		sList.set(indexInDomain, realC.multiply(r).add(t));
		cList.set(indexInDomain, realC);
	}

	/**
	 * Verifies the given ciphertext given the ciphertext, public key, and
	 * domain.
	 *
	 * @param ciphertext the ciphertext
	 * @param pubKey the public key
	 * @param domain the domain
	 * @return true if the proof is valid
	 */
	public boolean verify(ElgamalCiphertext ciphertext, PublicKey pubKey,
			List/*<AdderInteger>*/ domain) {
		p = pubKey.getP();
		q = pubKey.getQ();
		AdderInteger g = pubKey.getG();
		AdderInteger h = pubKey.getH();
		AdderInteger f = pubKey.getF();

		AdderInteger bigG = ciphertext.getG();
		AdderInteger bigH = ciphertext.getH();

		AdderInteger cChoices = new AdderInteger(AdderInteger.ZERO, q);

		StringBuffer sb = new StringBuffer(4096);

		sb.append(g);
		sb.append(h);
		sb.append(bigG);
		sb.append(bigH);

		int size = cList.size();

		for (int i = 0; i < size; i++) {
			AdderInteger d = (AdderInteger) domain.get(i);
			AdderInteger fpow = f.pow(d);
			AdderInteger s = (AdderInteger) sList.get(i);
			AdderInteger c = (AdderInteger) cList.get(i);
			AdderInteger negC = c.negate();

			cChoices = cChoices.add(c);

			sb.append(g.pow(s).multiply(bigG.pow(negC)));
			sb.append(h.pow(s).multiply(bigH.divide(fpow).pow(negC)));
		}

		String cHash = Util.sha1(sb.toString());
		AdderInteger newC = new AdderInteger(cHash, q, 16).mod(q);

		return (cChoices.equals(newC));
	}

	/**
	 * Creates a <tt>MembershipProof</tt> from the string standard representation
	 * as described in the {@link #toString} method.
	 *
	 * @param  s a string that specifies a <tt>MembershipProof</tt>
	 * @return a <tt>MembershipProof</tt> with the specified values
	 */
	public static MembershipProof fromString(String s) {
		StringTokenizer st = new StringTokenizer(s, "pyzsc", true);
		int numTokens = st.countTokens() - 2;

		if ((numTokens % 8) != 0) {
			throw new
			InvalidMembershipProofException("number of tokens not divisible by 8");
		}

		int count = numTokens / 8;

		try {
			if (!st.nextToken().equals("p")) {
				throw new InvalidMembershipProofException("expected token: `p\'");
			}

			AdderInteger p = new AdderInteger(st.nextToken());

			AdderInteger q
			= p.subtract(AdderInteger.ONE).divide(AdderInteger.TWO);

			List<AdderInteger> yList
			= new ArrayList<AdderInteger>(count);

			for (int ySize = 0; ySize < count; ySize++) {
				if (!st.nextToken().equals("y")) {
					throw new
					InvalidMembershipProofException("expected token: `y\'");
				}

				yList.add(new AdderInteger(st.nextToken(), p));
			}

			List<AdderInteger> zList
			= new ArrayList<AdderInteger>(count);

			for (int zSize = 0; zSize < count; zSize++) {
				if (!st.nextToken().equals("z")) {
					throw new
					InvalidMembershipProofException("expected token: `z\'");
				}

				zList.add(new AdderInteger(st.nextToken(), p));
			}

			List<AdderInteger> sList
			= new ArrayList<AdderInteger>(count);

			for (int sSize = 0; sSize < count; sSize++) {
				if (!st.nextToken().equals("s")) {
					throw new
					InvalidMembershipProofException("expected token: `s\'");
				}

				sList.add(new AdderInteger(st.nextToken(), q));
			}

			List<AdderInteger> cList
			= new ArrayList<AdderInteger>(count);

			for (int cSize = 0; cSize < count; cSize++) {
				if (!st.nextToken().equals("c")) {
					throw new
					InvalidMembershipProofException("expected token: `c\'");
				}

				cList.add(new AdderInteger(st.nextToken(), q));
			}

			return new MembershipProof(p, q, yList, zList, sList, cList);
		} catch (NoSuchElementException nsee) {
			throw new InvalidMembershipProofException(nsee.getMessage());
		} catch (NumberFormatException nfe) {
			throw new InvalidMembershipProofException(nfe.getMessage());
		}
	}

	/**
	 * Returns a <code>String</code> object representing this
	 * <code>MembershipProof</code>.
	 * @return the string representation of this proof
	 */
	public String toString() {
		StringBuffer sb = new StringBuffer(4096);

		sb.append("p");
		sb.append(p);

		/*for (AdderInteger y : yList) {*/
		for (Iterator it = yList.iterator(); it.hasNext();) {
			AdderInteger y = (AdderInteger) it.next();
			sb.append("y");
			sb.append(y);
		}

		/*for (AdderInteger z : zList) {*/
		for (Iterator it = zList.iterator(); it.hasNext();) {
			AdderInteger z = (AdderInteger) it.next();
			sb.append("z");
			sb.append(z);
		}

		/*for (AdderInteger s : sList) {*/
		for (Iterator it = sList.iterator(); it.hasNext();) {
			AdderInteger s = (AdderInteger) it.next();
			sb.append("s");
			sb.append(s);
		}

		/*for (AdderInteger c : cList) {*/
		for (Iterator it = cList.iterator(); it.hasNext();) {
			AdderInteger c1 = (AdderInteger) it.next();
			sb.append("c");
			sb.append(c1);
		}

		return sb.toString();
	}

	/**
     * Method for interop with VoteBox's S-Expression system.
     * 
     * @return the S-Expression equivalent of this MembershipProof
     */
	public ASExpression toASE(){
		List<ASExpression> yListL = new ArrayList<ASExpression>();
		for(AdderInteger y : yList)
			yListL.add(y.toASE());

		List<ASExpression> zListL = new ArrayList<ASExpression>();
		for(AdderInteger z : zList)
			zListL.add(z.toASE());

		List<ASExpression> sListL = new ArrayList<ASExpression>();
		for(AdderInteger s : sList)
			sListL.add(s.toASE());

		List<ASExpression> cListL = new ArrayList<ASExpression>();
		for(AdderInteger c : cList)
			cListL.add(c.toASE());

		return new ListExpression(StringExpression.makeString("membership-proof"),
				p.toASE(),
				new ListExpression(yListL),
				new ListExpression(zListL),
				new ListExpression(sListL),
				new ListExpression(cListL));
	}
	
	/**
     * Method for interop with VoteBox's S-Expression system.
     * 
     * @param ase - S-Expression representation of a MembershipProof
     * @return the MembershipProof equivalent of ase
     */
	public static MembershipProof fromASE(ASExpression ase){
		ListExpression exp = (ListExpression)ase;
		
		if(!(exp.get(0)).toString().equals("membership-proof"))
			throw new RuntimeException("Not membership-proof");
		
		AdderInteger p = AdderInteger.fromASE(exp.get(1));
		
		List<AdderInteger> yList = new ArrayList<AdderInteger>();
		List<AdderInteger> zList = new ArrayList<AdderInteger>();
		List<AdderInteger> sList = new ArrayList<AdderInteger>();
		List<AdderInteger> cList = new ArrayList<AdderInteger>();
		
		ListExpression yListE = (ListExpression)exp.get(2);
		ListExpression zListE = (ListExpression)exp.get(3);
		ListExpression sListE = (ListExpression)exp.get(4);
		ListExpression cListE = (ListExpression)exp.get(5);
		
		for(int i = 0; i < yListE.size(); i++) yList.add(AdderInteger.fromASE(yListE.get(i)));
		for(int i = 0; i < zListE.size(); i++) zList.add(AdderInteger.fromASE(zListE.get(i)));
		for(int i = 0; i < sListE.size(); i++) sList.add(AdderInteger.fromASE(sListE.get(i)));
		for(int i = 0; i < cListE.size(); i++) cList.add(AdderInteger.fromASE(cListE.get(i)));
		
		AdderInteger q = p.subtract(AdderInteger.ONE).divide(AdderInteger.TWO);
		
		return new MembershipProof(p, q, yList, zList, sList, cList);
	}
}
