package uk.ac.surrey.pav.misc;

import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.math.BigInteger;
import java.security.PrivateKey;
import java.security.PublicKey;
import java.security.interfaces.RSAPrivateKey;
import java.security.interfaces.RSAPublicKey;

import uk.ac.surrey.pav.ballotform.BallotFormPaper;
import uk.ac.surrey.pav.common.HexConstructor;

public class TestBigInteger {

	/**
	 * @param args
	 * @throws IOException 
	 * @throws FileNotFoundException 
	 * @throws ClassNotFoundException 
	 */
	public static void main(String[] args) throws FileNotFoundException, IOException, ClassNotFoundException {
		
		//Load private key from file
		ObjectInputStream objectIn = new ObjectInputStream(new FileInputStream("C:/votecomp/Administrator_private_key.ppk"));
		PrivateKey privateKey = (PrivateKey)objectIn.readObject();

		//Load public key from file
		objectIn = new ObjectInputStream(new FileInputStream("C:/votecomp/Administrator_public_key.ppk"));
		PublicKey publicKey = (PublicKey)objectIn.readObject();

		String hashAsHexString = "aa6001e023e484ddd72477a66b232e18";
		String signedHashAsHexString = "271f146a402598f815399ac1e3e58e5e0bec5036ba3afc84d0b727f97827da554e349f9d8e76d39b5f97249a70ca827fb9362621de610a43762e5dd3a3ba5f0c732d2b4251d00218dda12987e60fd49c9bf0049a6fefbd14c4c2c22026ebfc4f6265592afe5c85401d06fe60c49e2a6e64f2105bad20b67b398efe9503c65cd2";
		
		System.out.println("Hash as hex:                 " + hashAsHexString);
		BigInteger hashBigInt = new BigInteger(HexConstructor.hexStringToByteArray(hashAsHexString));
		System.out.println("... to bigint:               " + hashBigInt);
		BigInteger signedHashBigInt = (new BigInteger(BallotFormPaper.addHashSignature(hashBigInt.toByteArray(), privateKey)));
		System.out.println("... signed:                  " + signedHashBigInt);
		System.out.println("... to hex:                  " + HexConstructor.byteArrayToHexString(signedHashBigInt.toByteArray()));
		System.out.println("");
		
		System.out.println("Hash unhex sign unsign hex:  " + HexConstructor.byteArrayToHexString(BallotFormPaper.removeHashSignature(BallotFormPaper.addHashSignature(HexConstructor.hexStringToByteArray(hashAsHexString), privateKey), publicKey)));
		System.out.println("");

		System.out.println("Signed hash as hex:          " + signedHashAsHexString);
		signedHashBigInt = new BigInteger(HexConstructor.hexStringToByteArray(signedHashAsHexString));
		//signedHashBigInt = new BigInteger(signedHashAsHexString, 16);
		System.out.println("... to bigint:               " + signedHashBigInt);
		//BigInteger unsignedSignedHashBigInt = signedHashBigInt.modPow(((RSAPublicKey)publicKey).getPublicExponent(), ((RSAPublicKey)publicKey).getModulus());
		BigInteger unsignedSignedHashBigInt = new BigInteger(BallotFormPaper.removeHashSignature(signedHashBigInt.toByteArray(), publicKey));
		System.out.println("... unsigned:                " + unsignedSignedHashBigInt);
		System.out.println("... to hex:                  " + HexConstructor.byteArrayToHexString(unsignedSignedHashBigInt.toByteArray()));
		System.out.println("");
		
		/*
		BigInteger signedBigInt = hashBigInt.modPow(((RSAPrivateKey)privateKey).getPrivateExponent(), ((RSAPrivateKey)privateKey).getModulus());
		System.out.println("Signed hash bigint           " + signedBigInt);
		String signedBigIntAsHex = HexConstructor.byteArrayToHexString(signedBigInt.toByteArray());
		System.out.println("... to hex:                  " + signedBigIntAsHex);
		//BigInteger unhexedSignedBigIntAsHex = new BigInteger(HexConstructor.hexStringToByteArray(signedBigIntAsHex));
		BigInteger unhexedSignedBigIntAsHex = new BigInteger(signedBigIntAsHex, 16);
		System.out.println("... to bigint:               " + unhexedSignedBigIntAsHex);
		BigInteger unsignedBigInt = unhexedSignedBigIntAsHex.modPow(((RSAPublicKey)publicKey).getPublicExponent(), ((RSAPublicKey)publicKey).getModulus());
		System.out.println("... unsigned:                " + unsignedBigInt);
		System.out.println("... to hex:                  " + HexConstructor.byteArrayToHexString(unsignedBigInt.toByteArray()));
		*/
		
	}

}
