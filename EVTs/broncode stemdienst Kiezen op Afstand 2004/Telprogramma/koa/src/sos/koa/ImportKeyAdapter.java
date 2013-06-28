/*
 * JML specification Copyright 2004 SoS Group, University of Nijmegen
 */

package sos.koa;

import java.awt.*;
import java.awt.event.*;
import java.io.*;
import java.security.*;
import java.security.interfaces.*;
import java.security.spec.*;
import java.util.*;

import java.security.InvalidKeyException;
import java.security.KeyException;
import java.security.PrivateKey;
import java.security.PublicKey;
import java.security.interfaces.RSAPrivateKey;
import java.security.interfaces.RSAPublicKey;
import javax.crypto.spec.PBEKeySpec;
import javax.crypto.spec.PBEParameterSpec;

import javax.crypto.Cipher;
import javax.crypto.NoSuchPaddingException;
import javax.crypto.SecretKey;
import javax.crypto.SecretKeyFactory;

import javax.swing.*;

/**
 * Class to import both private and public key file.
 *
 * @version $Id: ImportKeyAdapter.java,v 1.24 2004/05/25 13:06:17 hubbers Exp $
 *
 * @author Martijn Oostdijk (martijno@cs.kun.nl)
 */
public class ImportKeyAdapter extends Task
{
   /** The type of encryption used to wrap the key. */
   private static final String KEY_DECRYPTION_ALGORITHM = "PBEWithMD5AndDES";

   /** The cryptographic type of the wrapped key is RSA. */
   private static final String RSA_ALGORITHM = "RSA";

   /** The salt used in constructing the PBE cipher. */
   private static final byte [] SALT =
      { (byte)0x19, (byte)0x36, (byte)0x78, (byte)0x99,
        (byte)0x52, (byte)0x3E, (byte)0xEA, (byte)0xF2 };

   /** The iteration count used by the PBE cipher. */
   private static final int ITERATION_COUNT = 20;

   /** The type of key, either PRIVATE_KEYTYPE or PUBLICKEYTYPE. */
   private /*@ spec_public @*/ int keyType;

   /*@ invariant keyType == PRIVATE_KEYTYPE || keyType == PUBLIC_KEYTYPE;
    */

   /**
    * Constructs this adapter.
    *
    * <pre><jml>
    * normal_behavior
    *    requires keyType == PRIVATE_KEYTYPE || keyType == PUBLIC_KEYTYPE;
    *    modifies \everything;
    * </jml></pre>
    */
   public ImportKeyAdapter(int keyType) {
      this.keyType = keyType;
   }

   String getTitle() {
      switch (keyType) {
         case PUBLIC_KEYTYPE:
            return IMPORT_PUBLIC_KEY_TASK_MSG;
         case PRIVATE_KEYTYPE:
            return IMPORT_PRIVATE_KEY_TASK_MSG;
      }
      return null;
   }

   String getSuccessMessage() {
      return IMPORT_KEY_SUCCESS_MSG;
   }

   String getFailureMessage() {
      return IMPORT_KEY_FAILURE_MSG;
   }

   /*@ pure */ boolean isPreStateAllowed(int state) {
      if (keyType == PUBLIC_KEYTYPE) {
         return (state == PRIVATE_KEY_IMPORTED_STATE);
      } else {
         return (state == VOTES_IMPORTED_STATE);
      }
   }

   /*@ pure */ int getSuccessState() {
      if (keyType == PUBLIC_KEYTYPE) {
         return PUBLIC_KEY_IMPORTED_STATE;
      } else {
         return PRIVATE_KEY_IMPORTED_STATE;
      }
   }

   /*@
     @ also
     @ assignable objectState;
     @*/
   void doAction() throws KOAException {
      Key rsaKey = null;
      File keyFile = popupGetFile(".key", "Sleutelbestanden (*.key)");

      try {

         /* Read file and do some checks... */
         FileInputStream keyIn = new FileInputStream(keyFile);
         byte[] wrappedKey = new byte[keyIn.available()];
         keyIn.read(wrappedKey);

         /* Ask user for password... */
         String passwd = popupGetPassword();

         /* Construct the pbe key from the password... */
         PBEKeySpec pbeKeySpec = new PBEKeySpec(passwd.toCharArray());
         PBEParameterSpec pbeParamSpec =
            new PBEParameterSpec(SALT,ITERATION_COUNT);
         SecretKeyFactory factory =
            SecretKeyFactory.getInstance(KEY_DECRYPTION_ALGORITHM);
         SecretKey pbeKey = factory.generateSecret(pbeKeySpec);

         Cipher pbeCipher = Cipher.getInstance(KEY_DECRYPTION_ALGORITHM);
         pbeCipher.init(Cipher.UNWRAP_MODE,pbeKey,pbeParamSpec);
         /* Get the rsa key from the file... */
         if (keyType == PRIVATE_KEYTYPE) {
            rsaKey =
               pbeCipher.unwrap(wrappedKey,RSA_ALGORITHM,Cipher.PRIVATE_KEY);
            MenuPanel.getTheMenuPanel().setPrivateKey((PrivateKey)rsaKey);
         } else if (keyType == PUBLIC_KEYTYPE) {
            rsaKey =
               pbeCipher.unwrap(wrappedKey,RSA_ALGORITHM,Cipher.PUBLIC_KEY);

            MenuPanel.getTheMenuPanel().setPublicKey((PublicKey)rsaKey);
            RSAPrivateKey privkey =
               (RSAPrivateKey)MenuPanel.getTheMenuPanel().getPrivateKey();
            boolean match =
               (privkey != null) &&
               privkey.getModulus().equals(((RSAPublicKey)rsaKey).getModulus());
            if (!match) {
               throw new KOAException("Private en publieke sleutel\n"
                                      + "vormen geen paar!");
            }
         }
      } catch (InvalidKeyException ivke) {
         throw new KOAException("Bestand bevat geen sleutel\n"
                                + "of verkeerde passphrase!");
      } catch (FileNotFoundException fnfe) {
         throw new KOAException("Bestand niet gevonden!");
      } catch (InvalidKeySpecException ikse) {
         throw new KOAException("Crypto bibliotheek\n"
                                + "ondersteunt algoritme niet!");
      } catch (NoSuchAlgorithmException nsae) {
         throw new KOAException("Crypto bibliotheek\n"
                                + "ondersteunt algoritme niet!");
      } catch (NoSuchPaddingException nspe) {
         throw new KOAException("Crypto bibliotheek\n"
                                + "ondersteunt algoritme niet!");
      } catch (InvalidAlgorithmParameterException iape) {
         throw new KOAException("Crypto bibliotheek\n"
                                + "ondersteunt algoritme niet!");
      } catch (IOException ioe) {
         throw new KOAException(ioe);
      }
   }

   void logStarted() {
   }

   void logOpenedFile(File keyFile) {
      Date keyFileModification = new Date(keyFile.lastModified());
      if (keyType == PUBLIC_KEYTYPE) {
         AuditLog.setImportPubKeyFileName(keyFile.toString());
         AuditLog.setImportPubKeyFileTimestamp(keyFileModification.toString());
      } else {
         AuditLog.setImportPrivKeyFileName(keyFile.toString());
         AuditLog.setImportPrivKeyFileTimestamp(keyFileModification.toString());
      }
   }

   void logFailed(String reason) {
      if (keyType == PUBLIC_KEYTYPE) {
         AuditLog.setImportPubKeyError(reason);
      } else {
         AuditLog.setImportPubKeyError(reason);
      }
   }

   void logCompleted() {
      if (keyType == PUBLIC_KEYTYPE) {
         AuditLog.setImportPubKeySuccess(true);
         AuditLog.setKeypairSuccess(true);
      } else {
         AuditLog.setImportPrivKeySuccess(true);
      }
   }
}

