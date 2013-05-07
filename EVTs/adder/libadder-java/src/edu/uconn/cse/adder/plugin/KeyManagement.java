package edu.uconn.cse.adder.plugin;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.Iterator;
import java.util.List;

import edu.uconn.cse.adder.AdderInteger;
import edu.uconn.cse.adder.InvalidPolynomialException;
import edu.uconn.cse.adder.InvalidPrivateKeyException;
import edu.uconn.cse.adder.InvalidPublicKeyException;
import edu.uconn.cse.adder.Polynomial;
import edu.uconn.cse.adder.PrivateKey;
import edu.uconn.cse.adder.PublicKey;
import edu.uconn.cse.adder.Util;
import edu.uconn.cse.adder.Vote;

/**
 * Key management.
 *
 * @author David Walluck
 * @version $LastChangedRevision$ $LastChangedDate$
 * @since 0.0.1
 */
final class KeyManagement {
    static final String ADDER_PUBLIC_KEY_FILE   = "pubkey.adder";
    static final String ADDER_SECRET_SHARE_FILE = "privkey.adder";
    static final String ADDER_POLYNOMIAL_FILE   = "polynomial.adder";
    static final String ADDER_PRIVATE_KEY_FILE2 = "privkey2.adder";

    /** Don't instantiate me. */
    private KeyManagement() {

    }

    static boolean init() {
        return myCreateDirectory(getAdderDirectory());
    }

    static String getAdderDirectory() {
        /* java.util.PropertyPermission user.home read */
        return System.getProperty("user.home")
            + File.separator + ".adder-java";
    }

    static String getAdderDirectory(String user, String procedure) {
        /* java.util.PropertyPermission read */
        return getAdderDirectory()
            + File.separator + procedure
            + File.separator + user;
    }

    static boolean checkDirectoryPermissions(String directory) {
        return true;
    }

    static boolean directoryExists(String directory) {
        /* java.io.FilePermission directory read */
        return new File(directory).isDirectory();
    }

    static boolean createDirectory(String directory) {
        /* java.io.FilePermission directory write */
        return new File(directory).mkdirs();
    }

    static boolean myCreateDirectory(String directory) {
        if (!directoryExists(directory)) {
            return (createDirectory(directory)
                    && checkDirectoryPermissions(directory));
        } else {
            return checkDirectoryPermissions(directory);
        }
    }

    static boolean createKeyDirectory(String user, String procedure) {
        if (!isValidUser(user) || !isValidProcedure(procedure)) {
           return false;
        }

        return myCreateDirectory(getAdderDirectory(user, procedure));
    }

    static Vote encryptVote(PublicKey key, List/*<AdderInteger>*/ choices) {
        return key.encrypt(choices);
    }

    static PublicKey readPublicKey(String keyFile) {
        BufferedReader br = null;
        PublicKey pubKey = null;

        try {
            /* java.io.FilePermission keyFile read */
            br = new BufferedReader(new FileReader(new File(keyFile)));
            String str = br.readLine();
            pubKey = PublicKey.fromString(str);
        } catch (FileNotFoundException fnfe) {
            throw new InvalidPublicKeyException(fnfe.getMessage());
        } catch (IOException ioe) {
            throw new InvalidPublicKeyException(ioe.getMessage());
        } finally {
            try {
                if (br != null) {
                    br.close();
                }
            } catch (IOException e) {

            }
        }

        return pubKey;
    }

    static Polynomial readPolynomial(String keyFile) {
        BufferedReader br = null;
        Polynomial poly = null;

        try {
            /* java.io.FilePermission keyFile read */
            br = new BufferedReader(new FileReader(new File(keyFile)));
            String str = br.readLine();
            poly = Polynomial.fromString(str);
        } catch (FileNotFoundException fnfe) {
            throw new InvalidPolynomialException(fnfe.getMessage());
        } catch (IOException ioe) {
            throw new InvalidPolynomialException(ioe.getMessage());
        } finally {
            try {
                if (br != null) {
                    br.close();
                }
            } catch (IOException e) {

            }
        }

        return poly;
    }

    static PrivateKey readPrivateKey(String keyFile) {
        BufferedReader br = null;
        PrivateKey privKey = null;

        try {
            /* java.io.FilePermission keyFile read */
            br = new BufferedReader(new FileReader(new File(keyFile)));
            String str = br.readLine();
            privKey = PrivateKey.fromString(str);
        } catch (FileNotFoundException fnfe) {
            throw new InvalidPrivateKeyException(fnfe.getMessage());
        } catch (IOException ioe) {
            throw new InvalidPrivateKeyException(ioe.getMessage());
        } finally {
            try {
                if (br != null) {
                    br.close();
                }
            } catch (IOException e) {

            }
        }

        return privKey;
    }

    static boolean writePublicKey(PublicKey pubKey, String keyFile) {
        try {
            /* java.io.FilePermission keyFile write */
            PrintWriter pw
                = new PrintWriter(new FileWriter(new File(keyFile)));
            pw.println(pubKey.toString());
            pw.close();
        } catch (FileNotFoundException fnfe) {
            return false;
        } catch (IOException ioe) {
            return false;
        }

        return true;
    }

    static boolean writePrivateKey(PrivateKey privKey, String keyFile) {
        try {
            /* java.io.FilePermission keyFile write */
            PrintWriter pw
                = new PrintWriter(new FileWriter(new File(keyFile)));
            pw.println(privKey.toString());
            pw.close();
        } catch (FileNotFoundException fnfe) {
            return false;
        } catch (IOException ioe) {
            return false;
        }

        return true;
    }

    static PublicKey readPubKey(String user, String procedure) {
        return readPublicKey(KeyManagement.getAdderDirectory(user, procedure)
               + File.separator + ADDER_PUBLIC_KEY_FILE);
    }

    static Polynomial readPoly(String user, String procedure)
        throws IOException {
        return readPolynomial(KeyManagement.getAdderDirectory(user, procedure)
               + File.separator + ADDER_POLYNOMIAL_FILE);
    }

    static boolean deletePoly(String user, String procedure) {
        String keyFile
            = getAdderDirectory(user, procedure) + File.separator
              + ADDER_POLYNOMIAL_FILE;
        /* java.io.FilePermission keyFile write */
        File file = new File(keyFile);

       if (file.exists()) {
          /* java.io.FilePermission keyFile delete */
          return file.delete();
       }

       return true;
    }

    static PrivateKey readPrivKey(String user, String procedure)
        throws IOException {
        String keyFile
            = getAdderDirectory(user, procedure) + File.separator
              + ADDER_SECRET_SHARE_FILE;
        return readPrivateKey(keyFile);
    }

    static boolean writePrivKey(String user, String procedure, String privKey) {
        boolean success = createKeyDirectory(user, procedure);

        if (!success) {
            return false;
        }

        try {
            String keyFile
                = getAdderDirectory(user, procedure) + File.separator
                  + ADDER_SECRET_SHARE_FILE;
            /* java.io.FilePermission keyFile write */
            PrintWriter pw
                = new PrintWriter(new FileWriter(new File(keyFile)));
            pw.println(privKey);
            pw.close();
        } catch (FileNotFoundException fnfe) {
            return false;
        } catch (IOException ioe) {
            return false;
        }

        return true;
    }

    static boolean writePolynomial(String user, String procedure,
                                   String polynomial) {
        boolean success = createKeyDirectory(user, procedure);

        if (!success) {
            return false;
        }

        try {
            String keyFile
                = getAdderDirectory(user, procedure) + File.separator
                  + ADDER_POLYNOMIAL_FILE;
            /* java.io.FilePermission keyFile write */
            PrintWriter pw
                = new PrintWriter(new FileWriter(new File(keyFile)));
            pw.println(polynomial);
            pw.close();
        } catch (FileNotFoundException fnfe) {
            return false;
        } catch (IOException ioe) {
            return false;
        }

        return true;
    }

    static PrivateKey readPrivKey2(String user, String procedure)
        throws IOException {
        PrivateKey privKey
            = readPrivateKey(getAdderDirectory(user, procedure)
              + File.separator + ADDER_PRIVATE_KEY_FILE2);

        return privKey;
    }

    static boolean writePrivKey2(String user, String procedure,
                                 String privKey) {
        boolean success = createKeyDirectory(user, procedure);

        if (!success) {
            return false;
        }

        try {
            String keyFile
                = getAdderDirectory(user, procedure) + File.separator
                  + ADDER_PRIVATE_KEY_FILE2;
            /* java.io.FilePermission keyFile write */
            PrintWriter pw
                = new PrintWriter(new FileWriter(new File(keyFile)));
            pw.println(privKey);
            pw.close();
        } catch (FileNotFoundException fnfe) {
            return false;
        } catch (IOException ioe) {
            return false;
        }

        return true;
    }

    static boolean createKeyPair(String user, String procedure,
                                 PublicKey pubKey) {
        boolean success = createKeyDirectory(user, procedure);

        if (!success) {
            return false;
        }

        PrivateKey privKey = pubKey.genKeyPair();

        String to;

        to = getAdderDirectory(user, procedure) + File.separator
             + ADDER_SECRET_SHARE_FILE;
        success = writePrivateKey(privKey, to);

        if (!success) {
            return false;
        }

        to = getAdderDirectory(user, procedure) + File.separator
             + ADDER_PUBLIC_KEY_FILE;

        return writePublicKey(pubKey, to);
    }

    static String decryptSum(String user, String procedure, Vote voteSum) {
        PrivateKey privateKey = null;

        try {
            privateKey = readPrivKey2(user, procedure);
        } catch (IOException e) {
            return "";
        }

        List/*<AdderInteger>*/ partialDecryptions
            = privateKey.partialDecrypt(voteSum);

        if (partialDecryptions == null
            || partialDecryptions.size() == 0) {
            return "";
        }

        Iterator it = partialDecryptions.iterator();

        StringBuffer sb = new StringBuffer(4096);
        sb.append("(");

        while (true) {
            AdderInteger i = (AdderInteger) it.next();
            sb.append(i.toString());

            if (it.hasNext()) {
                sb.append(", ");
            } else {
                sb.append(")");
                break;
            }
        }

        return sb.toString();
    }

    static String shortHash(Vote vote) {
        return vote.shortHash();
    }

    static boolean isValidUser(String user) {
        /* This assumes all alphanumeric usernames. */
        int size = user.length();

        for (int i = 0; i < size; i++) {
            if (!Character.isLetterOrDigit(user.charAt(i))) {
                return false;
            }
        }

        return true;
    }

    static boolean isValidProcedure(String procedure) {
        if (procedure.length() != 36) {
            return false;
        }

        int i = 0;

        for (i = 0; i < 8; i++) {
            if (!Util.isHexDigit(procedure.charAt(i))) {
                return false;
            }
        }

        if (procedure.charAt(i) != '-') {
            return false;
        }

        for (i = 9; i < 13; i++) {
            if (!Util.isHexDigit(procedure.charAt(i))) {
                return false;
            }
        }

        if (procedure.charAt(i) != '-') {
            return false;
        }

        for (i = 14; i < 18; i++) {
            if (!Util.isHexDigit(procedure.charAt(i))) {
                return false;
            }
        }

        if (procedure.charAt(i) != '-') {
            return false;
        }

        for (i = 19; i < 23; i++) {
            if (!Util.isHexDigit(procedure.charAt(i))) {
                return false;
            }
        }

        if (procedure.charAt(i) != '-') {
            return false;
        }

        for (i = 24; i < 36; i++) {
            if (!Util.isHexDigit(procedure.charAt(i))) {
                return false;
            }
        }

        return true;
    }
}
