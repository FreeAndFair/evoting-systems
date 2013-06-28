/*
 * JML specification Copyright 2004 SoS Group, University of Nijmegen
 */

package sos.koa;

import java.awt.*;
import java.awt.event.*;
import java.io.*;
import java.util.*;
import javax.swing.*;

import java.security.PrivateKey;
import java.security.Security;
import java.security.*;

import javax.crypto.Cipher;
import javax.crypto.SecretKey;
import javax.crypto.SecretKeyFactory;
import javax.crypto.spec.DESedeKeySpec;
import javax.crypto.spec.IvParameterSpec;

import java.io.IOException;
import java.io.UnsupportedEncodingException;
import java.security.InvalidKeyException;
import java.security.NoSuchAlgorithmException;
import java.security.NoSuchProviderException;
import java.security.spec.InvalidKeySpecException;
import javax.crypto.IllegalBlockSizeException;
import javax.crypto.NoSuchPaddingException;
import javax.crypto.BadPaddingException;

/**
 * Class to decrypt the votes.
 *
 * @version $Id: DecryptAdapter.java,v 1.46 2004/05/28 20:37:23 hubbers Exp $
 *
 * @author Martijn Oostdijk (martijno@cs.kun.nl)
 */
public class DecryptAdapter extends Task
{
   /** The salt value used to generate the session keys. */
   private static final byte [] SALT =
      { (byte)0x19, (byte)0x36, (byte)0x78, (byte)0x99,
        (byte)0x52, (byte)0x3E, (byte)0xEA, (byte)0xF2 };

   /** The algorithm used by the <code>rsaCipher</code>. */
   static final String RSA_ALGORITHM = "RSA";

   /** The algorithm used by the desedeCipher. */
   static final String DESEDE_DECRYPT_ALGORITHM = "DESede/CBC/PKCS7Padding";

   /** The RSA cipher for decrypting the session key. */
   /*@ spec_public */ Cipher rsaCipher; //@ in objectState;

   /** The session key cipher for decrypting the vote information. */
   /*@ spec_public */ Cipher desedeCipher; //@ in objectState;

   /** Indicates whether to keep decrypting. */
   /*@ spec_public */ boolean keepRunning; //@ in objectState;

   /** The number of votes decrypted this far. */
   /*@ spec_public */ int rowCount; //@ in objectState;

   /** A list containing errors encountered this far. */
   /*@ spec_public */ ArrayList errors; //@ in objectState;

   /**
    * Constructs this adapter.
    */
   public DecryptAdapter() {
      Security.insertProviderAt(new org.bouncycastle.jce.provider.BouncyCastleProvider(),2);
   }

   /*@ pure non_null */ String getTitle() {
      return DECRYPT_TASK_MSG;
   }

   /*@ pure non_null */ String getSuccessMessage() {
      if (errors != null && errors.size() > 0) {
         return DECRYPT_SUCCESS_MSG + "\n\n"
                + AuditLog.getImportVotesNrOfVotes() 
                + " stem"
                + (AuditLog.getImportVotesNrOfVotes() != 1 ? "men" : "")
                + " geïmporteerd.\n" 
                + errors.size() 
                + " stem" 
                + (errors.size() != 1 ? "men" : "") 
                + VOTES_IGNORED_SEE_MORE_INFO_MSG;
      } else {
         return DECRYPT_SUCCESS_MSG + "\n\n"
                + NO_ERRORS_MSG;
      }
   }

   /*@ pure non_null */ String getFailureMessage() {
      return DECRYPT_FAILURE_MSG;
   }

   /*@ pure non_null */ String getInfo() {
      return rowCount + " stem" + (rowCount != 1 ? "men":"") + " ontsleuteld.";
   }

   /*@ pure */ boolean isPreStateAllowed(int state) {
      return (state == PUBLIC_KEY_IMPORTED_STATE);
   }

   /*@ pure */ int getSuccessState() {
      return VOTES_DECRYPTED_STATE;
   }

   public /*@ pure */ boolean isProgressMonitoredTask() {
      return true;
   }

   /*@ also
     @ behavior
     @    assignable AuditLog.*;
    */
   void logStarted() {
      AuditLog.setDecryptTimestampStart(AuditLog.getCurrentTimestamp());
   }

   /*@ also
     @ behavior
     @    requires reason != null;
     @    assignable AuditLog.*;
    */
   void logFailed(String reason) {
      AuditLog.setDecryptSuccess(false);
      String[] err = { reason };
      AuditLog.setDecryptErrors(err);
   }

   /*@ also
     @ behavior
     @    assignable AuditLog.*;
    */
   void logCompleted() {
      AuditLog.setDecryptSuccess(true);
      AuditLog.setDecryptNrOfVotes(rowCount);
      AuditLog.setDecryptErrors(getErrors());
      AuditLog.setDecryptTimestampEnd(AuditLog.getCurrentTimestamp());
   }

   /**
    * Decrypts the votes in <code>rawVotes</code>.
    *
    * @throws KOAException if decryption failed.
    */
   /*@ also
     @ behavior
     @    requires MenuPanel.getTheMenuPanel().rawVotes != null;
     @    assignable \everything;
     @    ensures MenuPanel.getTheMenuPanel().rawVotes != null;
    */
   void doAction() throws KOAException {
      errors = new ArrayList();
      try {
         setMaxSubTasks(MenuPanel.getTheMenuPanel().getRawVotes().size());
         PrivateKey rsakey = MenuPanel.getTheMenuPanel().getPrivateKey();
         rsaCipher = Cipher.getInstance(RSA_ALGORITHM,"BC");
         rsaCipher.init(Cipher.DECRYPT_MODE,rsakey);
         desedeCipher = Cipher.getInstance(DESEDE_DECRYPT_ALGORITHM,"BC");
         ArrayList rawVotes = MenuPanel.getTheMenuPanel().getRawVotes();
         keepRunning = true;
         rowCount = 0;
         File baseDir = new File(BASEDIR);
         File outDir = new File(baseDir, OUTDIR);
         outDir.mkdirs();
         File outFile = new File(outDir, DECRYPTEDFILE);
         DataOutputStream decryptFile =
            new DataOutputStream(new FileOutputStream(outFile));
         for (int i = 0; i < rawVotes.size(); i++) {
            if (!keepRunning) {
               throw new KOAException(TASK_CANCELED_MSG);
            }
            Object vote = rawVotes.get(i);
            if (vote instanceof byte[]) {
               try {
                  byte[] encryptedVote = (byte[])vote;
                  String decryptedVote = decrypt(encryptedVote);
                  decryptFile.writeBytes(decryptedVote + "\n");
                  rawVotes.set(i,decryptedVote);
                  rowCount++;
               } catch (KOAException ke){
                  // Something went wrong decrypting this vote.
                  // Do not count this vote as being decrypted.
                  // We replace the vote by an error message.
                  // Add dummy so CountAdapter knows that decryption failed.
                  rawVotes.set(i,DECRYPT_ERROR_TAG + ke.getMessage());
                  errors.add(("Rij index " + i +": " + ke.getMessage()));
                  // The extra '(...)' are used to avoid a jmlc bug.
               } catch (Exception e){
                  // Something unknown went wrong decrypting this vote.
                  // Do not count this vote as being decrypted.
                  // We replace the vote by a default error message.
                  // Add dummy so CountAdapter knows that decryption failed.
                  rawVotes.set(i,DECRYPT_ERROR_TAG + e.getMessage());
                  errors.add(("\nRij index " + i +": " + e.getMessage()));
                  // The extra '(...)' are used to avoid a jmlc bug.
               }
            } else if (vote instanceof String) {
               // apparently already decrypted this one...
               // increase rowCount to keep the figures of decrypted votes
               // correct.
               rowCount++;
            }

            if (rowCount % 100 == 0) {
               setSubTaskCount(rowCount);
            }

         }
         decryptFile.close();
      } catch (KOAException ke) {
         throw new KOAException(ke.getMessage());
      } catch (NoSuchProviderException nspre) {
         throw new KOAException("Crypto bibliotheek\n"
                 + "niet gevonden!");
      } catch (NoSuchAlgorithmException nsae) {
         throw new KOAException("Crypto bibliotheek\n"
                 + "ondersteunt algoritme niet!");
      } catch (InvalidKeyException ike) {
         throw new KOAException("Crypto bibliotheek\n"
                 + "ondersteunt sleutel niet!");
      } catch (NoSuchPaddingException nspae) {
         throw new KOAException("Crypto bibliotheek\n"
                 + "ondersteunt encoding niet!");
      } catch (Exception ex) { 
         throw new KOAException("Onbekende fout");
      }
   }

   /**
    * Interrupts the execution of <code>doAction</code>.
    */
   /*@
     @ also
     @ assignable objectState;
     @ ensures !keepRunning;
     @*/
   void stopAction() {
      keepRunning = false;
   }

   /**
    * Decrypts one vote.
    *
    * @param encryptedVote the vote to decrypt.
    *
    * @return the decrypted vote.
    *
    * @throws KOAException if decryption failed.
    */
   /*@ private behavior
     @    requires encryptedVote != null;
     @    assignable rsaCipher.*, desedeCipher.*;
     @    signals(KOAException) true;
    */
   private /*@ non_null */ String decrypt(byte[] encryptedVote)
   throws KOAException {
      try {
         ByteArrayInputStream bytesIn =
            new ByteArrayInputStream(encryptedVote);
         DataInputStream dataIn = new DataInputStream(bytesIn);

         /* Get the session key... */
         int len1 = dataIn.readInt();
         // To avoid OutOfMemoryError if there is rubbish in the encrypted vote
         if (len1 > MAX_KEY_LENGTH) {
            throw new KOAException("Sessiesleutel langer dan "
                                   + MAX_KEY_LENGTH + ": " + len1);
         }
         byte[] wrappedSessionKey = new byte[len1];
         dataIn.read(wrappedSessionKey);
         byte[] sessionkeyData = rsaCipher.doFinal(wrappedSessionKey);

         /* Only the last 24 bytes are significant... */
         byte[] desedekeyData = new byte[24];
         System.arraycopy(sessionkeyData,39,desedekeyData,0,24);
         IvParameterSpec ivParamSpec = new IvParameterSpec(SALT);
         SecretKeyFactory factory = SecretKeyFactory.getInstance("DESede","BC");
         SecretKey desedeKey =
            factory.generateSecret(new DESedeKeySpec(desedekeyData));
         desedeCipher.init(Cipher.DECRYPT_MODE,desedeKey,ivParamSpec);

         /* Decrypt the vote... */
         int len2 = dataIn.readInt();
         // To avoid OutOfMemoryError if there is rubbish in the encrypted vote
         if (len2 > MAX_ENCRYPTED_VOTE_LENGTH) {
            throw new KOAException("Versleutelde stem langer dan "
                                   + MAX_ENCRYPTED_VOTE_LENGTH + ": " + len2);
         }
         byte[] ciphertext = new byte[len2];
         dataIn.read(ciphertext);
         // Note: dataIn should be empty now...
         if (dataIn.read(new byte[1]) > 0) {
            throw new KOAException("Overbodige bytes gevonden in versleutelde stem");
         }
         byte[] plaintext = desedeCipher.doFinal(ciphertext);
         byte[] voteBytes = new byte[plaintext.length - 5];
         System.arraycopy(plaintext,5,voteBytes,0,voteBytes.length);

         return new String(voteBytes,"UTF-8");
      } catch (InvalidAlgorithmParameterException iape) {
         throw new KOAException("Crypto fout: "
                 + "ongeldige algoritme parameter!");
      } catch (NoSuchProviderException nspre) {
         throw new KOAException("Crypto fout: "
                 + "provider niet gevonden!");
      } catch (BadPaddingException bpe) {
         throw new KOAException("Crypto fout: "
                 + "slechte padding!");
      } catch (IllegalBlockSizeException ibse) {
         throw new KOAException("Crypto fout: "
                 + "bibliotheek ondersteunt blocksize niet!");
      } catch (NoSuchAlgorithmException nsae) {
         throw new KOAException("Crypto fout: "
                 + "bibliotheek ondersteunt algoritme niet!");
      } catch (InvalidKeyException ike) {
         throw new KOAException("Crypto fout: "
                 + "bibliotheek ondersteunt sleutel niet!");
      } catch (InvalidKeySpecException ikse) {
         throw new KOAException("Crypto fout: "
                 + "bibliotheek ondersteunt sleutel niet!");
      } catch (IOException ioe) {
         throw new KOAException("Input/output fout!");
      }
   }

   /*@ pure non_null */ Object getAdditionalInfo() {
      int height = Math.min(errors.size() + ADDITIONAL_INFO_EXTRA,
                                      ADDITIONAL_INFO_MAX_HEIGHT);
      JTextArea area = new JTextArea(height,ADDITIONAL_INFO_MAX_WIDTH);
      StringBuffer additionalInfo = new StringBuffer();
      if (errors.size() > 0) {
         additionalInfo.append("De volgende fouten zijn geconstateerd:\n");
         for (int i = 0; i < errors.size(); i++) {
            additionalInfo.append(errors.get(i).toString());
            additionalInfo.append("\n");
         }
      } else {
         additionalInfo.append("Er zijn geen fouten opgetreden bij het ontsleutelen.");
      }
      area.setText(additionalInfo.toString());
      area.setEditable(false);
      return new JScrollPane(area);
   }

   /*@ pure */ boolean isAdditionalInfoAvailable() {
      return true;
   }

   /**
    * Gets the errors encountered during execution of this task.
    *
    * @return an array of error strings.
    */
   /*@ pure non_null */ String[] getErrors() {
      String[] result = new String[errors.size()];
      errors.toArray(result);
      return result;
   }
}

