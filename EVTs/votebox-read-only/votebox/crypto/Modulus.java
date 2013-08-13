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

import java.math.BigInteger;
import java.util.Random;

public class Modulus {
    // half-way between 1024 and 2048
    public static final int DEFAULT_PRIME_BITS = 1536;
    // when testing a prime number, test to confidence 1-1/(2^PrimeConfidence)
    public static final int DEFAULT_PRIME_CONFIDENCE = 64;

    private static BigInteger one = BigInteger.ONE;
    private static BigInteger two = one.add(one);

    private Random randomBits = new java.security.SecureRandom();

    private BigInteger generator, modulus;
    private int numPrimeBits, primeConfidence;

    private void init(int numPrimeBits, int primeConfidence) {
        this.numPrimeBits = numPrimeBits;
        this.primeConfidence = primeConfidence;
        for (;;) {
            BigInteger p = new BigInteger(numPrimeBits, primeConfidence,
                    randomBits);
            BigInteger q = p.multiply(two).add(one);
            if (q.isProbablePrime(primeConfidence)) {
                for (;;) {
                    // random generator
                    BigInteger g = new BigInteger(numPrimeBits / 2, randomBits);
                    // square it
                    BigInteger gsq = g.multiply(g);
                    // g^2 needs to be less than q
                    if (gsq.compareTo(q) >= 0)
                        continue;
                    // degenerate case
                    if (gsq.equals(one))
                        continue;

                    // if we got here, that means that q is our modulus and gsq
                    // is our generator

                    generator = gsq;
                    modulus = q;
                    return;
                }
            }
        }
    }

    /**
     * establish a generator and modulus for Diffie-Hellman or El Gamal
     * encryption that satisfies the "standard" property where you don't leak
     * information if the information is a square or something or not.
     */
    public Modulus(int numPrimeBits, int primeConfidence) {
        init(numPrimeBits, primeConfidence);
    }

    /**
     * use default (cryptographically strong) values for prime bits and
     * confidence
     */
    public Modulus() {
        init(DEFAULT_PRIME_BITS, DEFAULT_PRIME_CONFIDENCE);
    }

    Modulus(int numPrimeBits, int primeConfidence, String generator,
            String modulus) {
        this.numPrimeBits = numPrimeBits;
        this.primeConfidence = primeConfidence;
        this.generator = new BigInteger(generator);
        this.modulus = new BigInteger(modulus);

        // generator should be smaller than modulus
        assert this.generator.compareTo(this.modulus) < 0;
        // modulus should be prime!
        assert this.modulus.isProbablePrime(this.primeConfidence);
    }

    /**
     * @return the generator
     */
    public BigInteger getGenerator() {
        return generator;
    }

    /**
     * @param generator
     *            the generator to set
     */
    public void setGenerator(BigInteger generator) {
        this.generator = generator;
    }

    /**
     * @return the modulus
     */
    public BigInteger getModulus() {
        return modulus;

    }

    /**
     * @param modulus
     *            the modulus to set
     */
    public void setModulus(BigInteger modulus) {
        this.modulus = modulus;
    }

    public java.util.Random getRandomSource() {
        return randomBits;
    }

    /**
     * returns a random integer less than the modulus
     * 
     * @return
     */
    public BigInteger getRandomValue() {
        BigInteger returnVal;

        for (;;) {
            returnVal = new BigInteger(numPrimeBits, randomBits);

            /*
             * the random number needs to be less than the modulus, otherwise
             * try again. This isn't exactly optimal, but it works.
             */
            if (returnVal.compareTo(modulus) < 0)
                return returnVal;
        }
    }

    public String toString() {
        return "NumPrimeBits: " + numPrimeBits + "\nPrimeConfidence: "
                + primeConfidence + "\nGenerator: " + generator.toString()
                + "\nModulus: " + modulus.toString();
    }

    /**
     * command-line utility to generate and print a modulus
     */
    public static void main(String args[]) {
        int numBits = 300;
        int confidence = 30;
        if (args.length == 2) {
            numBits = Integer.parseInt(args[0]);
            confidence = Integer.parseInt(args[1]);
        }
        else if (args.length != 0) {
            System.out.println("Usage: java Modulus [num-bits confidence]");
            System.exit(0);
        }
        Modulus m = new Modulus(numBits, confidence);
        System.out.println(m);
    }

}
