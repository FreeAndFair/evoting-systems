/**
  * This file is part of VoteBox.
  * 
  * VoteBox is free software: you can redistribute it and/or modify
  * it under the terms of the GNU General Public License version 3 as published by
  * the Free Software Foundation.
  * 
  * You should have received a copy of the GNU General Public License
  * along with VoteBox, found in the root of any distribution or
  * repository containing all or part of VoteBox.
  * 
  * THIS SOFTWARE IS PROVIDED BY WILLIAM MARSH RICE UNIVERSITY, HOUSTON,
  * TX AND IS PROVIDED 'AS IS' AND WITHOUT ANY EXPRESS, IMPLIED OR
  * STATUTORY WARRANTIES, INCLUDING, BUT NOT LIMITED TO, WARRANTIES OF
  * ACCURACY, COMPLETENESS, AND NONINFRINGEMENT.  THE SOFTWARE USER SHALL
  * INDEMNIFY, DEFEND AND HOLD HARMLESS RICE UNIVERSITY AND ITS FACULTY,
  * STAFF AND STUDENTS FROM ANY AND ALL CLAIMS, ACTIONS, DAMAGES, LOSSES,
  * LIABILITIES, COSTS AND EXPENSES, INCLUDING ATTORNEYS' FEES AND COURT
  * COSTS, DIRECTLY OR INDIRECTLY ARISING OUR OF OR IN CONNECTION WITH
  * ACCESS OR USE OF THE SOFTWARE.
 */

package votebox.crypto;

import junit.framework.TestCase;
import java.math.BigInteger;

public class ModulusTest extends TestCase {

	public void testModulus() {
		/*
		 * basic Diffie-Hellman math
		 */
		Modulus m = new Modulus(350, 30);
		BigInteger g = m.getGenerator();
		BigInteger p = m.getModulus();
		
		DHtest(g, p);
		EGtest(m, g, p);
	}
	
	public void testBigModulus() {
		String generatorString = "2016433053757341104328548369260225448420178492488839339195079012913740203550581367917603578255836416301659447919134003412324535550203014660828445101581073366209571738168074363709988319601925328131931318253630428729995428849722161812181697865734851328186930582450521842890975960480674438455535966317209024008129126238043911181175493403751902643934946891633427176473184689859908734305925529262343808427749985844869145540026953651663690952752846237422048321944844544";
		String modulusString = "4008068760601560176181090811191269958616134140815365887701703622467302386397406595276102404102599183050725940409230956564362213996772507892182603738589047156399535390756432494533344022585855134419330844861393164590002967760368498512584631894520092843017130932721913480603013976030676448835771942383177369284649842316969774775111437516174141766494812679525434402192524629913006391105583246025610804250839276542776846098833535690824388875515507421677606470210284503";
		int numPrimeBits = 1536;
		int primeConfidence = 80;
		
		Modulus m = new Modulus(numPrimeBits, primeConfidence, generatorString, modulusString);
		BigInteger g = m.getGenerator();
		BigInteger p = m.getModulus();

		DHtest(g, p);
		EGtest(m, g, p);
	}
	
	private void DHtest(BigInteger g, BigInteger p) {
		BigInteger aliceSecret = new BigInteger("12345");
		BigInteger bobSecret = new BigInteger("54321");
		
		/*
		 * the messages that alice and bob send to each other, respectively
		 */
		BigInteger atob = g.modPow(aliceSecret, p);
		BigInteger btoa = g.modPow(bobSecret, p);
		
		/*
		 * alice and bob now should be able to arrive at a shared secret
		 */
		BigInteger ashared = btoa.modPow(aliceSecret, p);
		BigInteger bshared = atob.modPow(bobSecret, p);
		
		assertTrue(ashared.compareTo(bshared) == 0);
	}
	
	private void EGtest(Modulus m, BigInteger g, BigInteger p) {
		BigInteger alicePrivate = m.getRandomValue();
		BigInteger alicePublic = g.modPow(alicePrivate, p);
		
		BigInteger plainText = new BigInteger("12345");
		
		BigInteger random = m.getRandomValue();
		BigInteger c1 = g.modPow(random, p);
		BigInteger c2 = plainText.multiply(alicePublic.modPow(random, p)).mod(p);
		
		BigInteger test = c2.multiply(c1.modPow(alicePrivate, p).modInverse(p)).mod(p);
		
		assertTrue(plainText.compareTo(test) == 0);
	}
}
