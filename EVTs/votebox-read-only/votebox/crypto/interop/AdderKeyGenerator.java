package votebox.crypto.interop;

import java.io.File;
import java.io.FileOutputStream;

import edu.uconn.cse.adder.PrivateKey;
import edu.uconn.cse.adder.PublicKey;

/**
 * Using this class, specify a destination directory, you can generate a single public/private key-pair
 * to be used by Adder when the NIZK switch is enabled.
 * @author Montrose
 *
 */
public class AdderKeyGenerator {

	/**
	 * @param args - args.length should == 1 and args[0] should be a path to the destination directory
	 */
	public static void main(String[] args) throws Exception{
		if(args.length != 1){
			System.out.println("Usage: java "+AdderKeyGenerator.class.getName()+" [destination directory]");
			System.exit(-1);
		}
		
		File destDir = new File(args[0]);
		
		if(!destDir.exists()){
			destDir.mkdirs();
		}else{
			if(!destDir.isDirectory()){
				System.out.println("Usage: java "+AdderKeyGenerator.class.getName()+" [destination directory]");
				System.exit(-1);
			}
		}
		
		
		System.out.println("Generating keys");
		PublicKey pubKey = PublicKey.makePartialKey(512);
		PrivateKey privKey = pubKey.genKeyPair();
		
		File pubFile = new File(destDir, "public.adder.key");
		File privFile = new File(destDir, "private.adder.key");
		
		System.out.println(pubFile.getAbsolutePath());
		System.out.println(privFile.getAbsolutePath());
		
		pubFile.createNewFile();
		privFile.createNewFile();
		
		FileOutputStream pubOut = new FileOutputStream(pubFile);
		FileOutputStream privOut = new FileOutputStream(privFile);
		
		//pubOut.write(pubKey.toString().getBytes());
		pubOut.write(pubKey.toASE().toVerbatim());
		//privOut.write(privKey.toString().getBytes());
		privOut.write(privKey.toASE().toVerbatim());
		
		pubOut.flush();
		privOut.flush();
		
		pubOut.close();
		privOut.close();
		
		System.exit(0);
	}

}
