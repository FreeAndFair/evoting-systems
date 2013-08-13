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

package auditorium;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.HashMap;
import java.util.jar.JarEntry;
import java.util.jar.JarFile;

import edu.uconn.cse.adder.PrivateKey;
import edu.uconn.cse.adder.PublicKey;

import sexpression.*;
import sexpression.stream.*;

/**
 * Simple keystore implementation which looks for keys and certificates in a
 * specified directory. Keys are represented by files named
 * <tt><i>nodeid</i>.key</tt> and containing an S-expression matching the
 * format expected by {@link Key}; similarly, certificate files are named
 * <tt><i>nodeid</i>.cert</tt> and contain an S-expression recognized by the
 * constructor for {@link Cert}.
 *
 * Keys and Certs are cached internally, so multiple requests for the same key
 * will not result in multiple loads from disk.
 * 
 * @see auditorium.Key
 * @see auditorium.Cert
 * @author kyle
 * 
 */
public class SimpleKeyStore implements IKeyStore {
	//Name of file containing keys/classes/etc for votebox (generally, a jar file)
	public static final String ROOT_JARS[] = {"votebox.jar", "supervisor.jar"}; 

	private final String _dir;
	private HashMap<String,Key>  _keyCache;
	private HashMap<String,Cert> _certCache;

	/**
	 * @param dir
	 *            This is the directory where the key and cert files are stored.
	 */
	public SimpleKeyStore(String dir) {
		_dir = dir;
		_keyCache  = new HashMap<String,Key>();
		_certCache = new HashMap<String,Cert>();
	}

	/**
	 * Load the key from a file in the "keys" directory.
	 * 
	 * @see auditorium.IKeyStore#loadKey(java.lang.String)
	 */
	public Key loadKey(String nodeid) throws AuditoriumCryptoException {
		if (! _keyCache.containsKey(nodeid)) {
			try {
				_keyCache.put(nodeid, 
						new Key( load( nodeid + ".key" ) ));
			}
			catch (Exception e) {
				throw new AuditoriumCryptoException( "loadKey(\"" + nodeid + "\")", e );
			}
		}

		return _keyCache.get(nodeid);
	}

	/**
	 * Load the published certificate from a file in the "keys" directory.
	 * 
	 * @see auditorium.IKeyStore#loadCert(java.lang.String)
	 */
	public Cert loadCert(String nodeid) throws AuditoriumCryptoException {
		if (! _certCache.containsKey(nodeid)) {
			try {
				_certCache.put(nodeid, 
						new Cert( load( nodeid + ".cert" ) ));
			}
			catch (Exception e) {
				throw new AuditoriumCryptoException( "loadCert(\"" + nodeid + "\")", e );
			}
		}

		return _certCache.get(nodeid);
	}

	public Object loadAdderKey(String nodeid){
		try{
			InputStream in = getInput(nodeid+".adder.key");

			ByteArrayOutputStream baos = new ByteArrayOutputStream();
			
			int i;
			while((i = in.read()) != -1){
				baos.write(i);
			}
			
			//String str = new String(baos.toByteArray());

			PublicKey pubKey = null;
			PrivateKey privKey = null;

			try{
				//pubKey = PublicKey.fromString(str);
				pubKey = PublicKey.fromASE(ASExpression.makeVerbatim(baos.toByteArray()));
			}catch(Exception e){
				e.printStackTrace();
				try{
					//privKey = PrivateKey.fromString(str);
					privKey = PrivateKey.fromASE(ASExpression.makeVerbatim(baos.toByteArray()));
				}catch(Exception f){f.printStackTrace();}
			}

			if(pubKey != null)
				return pubKey;

			if(privKey != null)
				return privKey;
		}catch(Exception e){
			throw new RuntimeException(e);
		}

		throw new RuntimeException("No adder key exists for nodeid: "+nodeid);
	}

	/**
	 * Loads a file for use in the KeyStore.<BR>
	 * First searches the ROOT_JAR, if it exists.<BR>
	 * Then looks for the path in the filesystem.<BR>
	 * The path itself is derived from _dir (_dir + "/" + file, approximately).
	 * 
	 * @param file - The file to load
	 * @return An ASExpression representing the file resource
	 * @throws AuditoriumCryptoException - Should any exception occur during processing.
	 */
	private ASExpression load(String file) throws AuditoriumCryptoException {
		/*String path = _dir + "/" + file; // note that "/" is the classLoader's path component separator char
        try {
            InputStream stream = getClass().getResourceAsStream(path);
			if (stream == null)
                throw new FileNotFoundException(path);

            return new ASEInputStreamReader( stream ).read();
        }
        catch (Exception e) {
            throw new AuditoriumCryptoException( "load(); path=\"" + path + "\"", e );
        }*/

		try {
			InputStream stream = getInput(file);

			return new ASEInputStreamReader(stream).read();
		} catch (IOException e1) {
			throw new AuditoriumCryptoException("load(\""+file+"\")", e1);
		} catch (InvalidVerbatimStreamException e1) {
			throw new AuditoriumCryptoException("load(\""+file+"\")", e1);
		}
	}
	
	/**
	 * Opens a stream for reading a key.
	 * 
	 * @param file - the name of the file that contains the key.  This does not include the path to the key
	 * @return an open InputStream to read from.
	 * @throws AuditoriumCryptoException - If the key cannot be found, or an error occurs
	 */
	private InputStream getInput(String file) throws AuditoriumCryptoException{
		InputStream stream = getClass().getResourceAsStream(_dir+"/"+file); // "/" is the classloaders path component, not a hardcoded unix style path component separator
		// leave it alone
		
		if(stream != null)
			return stream;
		
		//This is very ineligent, but only comes into play in development scenarios
		//Worth removing for a proper "deployment"

		//Check each jar that might have a keystore
		
		boolean[] jarsExist = new boolean[ROOT_JARS.length];

		String entry = _dir;
		if(!entry.endsWith("/"))
			entry += "/" + file;
		else
			entry += file;

		for(int i = 0; i < ROOT_JARS.length; i++){
			File jarFile = new File(ROOT_JARS[i]);

			if(jarFile.exists())
				jarsExist[i] = true;

			try{
				InputStream in = null;

				if(jarFile.exists()){
					JarFile vbJar = new JarFile(jarFile);

					JarEntry jEntry = null;

					if(entry.startsWith("/"))
						jEntry = vbJar.getJarEntry(entry.substring(1));
					else
						jEntry = vbJar.getJarEntry(entry);

					in = vbJar.getInputStream(jEntry);
				}//if

				/*ASExpression exp = new ASEInputStreamReader(in).read();

				in.close();

				return exp;*/
				
				if(in != null)
					return in;
			}catch(Exception e){
				continue;
			}//catch
		}//for

		//If that fails, check the working directory
		try{
			File rootFile = new File(entry.replace('/', File.separatorChar));

			if(!rootFile.exists() && entry.startsWith("/"))
				rootFile = new File(entry.substring(1).replace('/', File.separatorChar));

			InputStream in = new FileInputStream(rootFile);

			/*ASExpression exp = new ASEInputStreamReader(in).read();

			in.close();

			return exp;*/
			
			if(in != null)
				return in;
		}catch(Exception e){
			String msg = "load(); path = \""+entry+"\"";

			for(int i = 0; i < ROOT_JARS.length; i++)
				if(jarsExist[i])
					msg+=" with \""+ROOT_JARS[i]+"\" found";

			throw new AuditoriumCryptoException( msg, e );
		}//catch
		
		throw new AuditoriumCryptoException("No key found for \""+file+"\"", null);
	}
}
