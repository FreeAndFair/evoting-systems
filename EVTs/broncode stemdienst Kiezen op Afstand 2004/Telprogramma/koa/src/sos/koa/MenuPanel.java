/*
 * JML specification Copyright 2004 SoS Group, University of Nijmegen
 */

package sos.koa;

import java.awt.*;
import java.awt.event.*;
import java.io.*;
import java.security.*;
import java.util.*;
import javax.swing.*;

/**
 * This class is the top-most class of the system and tracks and
 * controls the overall tally process.
 *
 * @version $Id: MenuPanel.java,v 1.64 2004/05/25 13:06:17 hubbers Exp $
 *
 * @author Martijn Oostdijk (martijno@cs.kun.nl)
 */

public class MenuPanel extends JPanel implements KOAConstants
{
  /** The (single) menu panel instance. */

  private static /*@ spec_public non_null */ MenuPanel theInstance;

  static {
     theInstance = new MenuPanel();
  }

  /*@ constraint \old(theInstance) == theInstance;
   */

  /** The state of the application. */
  /*@ spec_public */ int state; //@ in objectState;

  /*@ invariant state == INIT_STATE ||
    @           state == CLEARED_STATE ||
    @           state == CANDIDATES_IMPORTED_STATE ||
    @           state == VOTES_IMPORTED_STATE ||
    @           state == PRIVATE_KEY_IMPORTED_STATE ||
    @           state == PUBLIC_KEY_IMPORTED_STATE ||
    @           state == VOTES_DECRYPTED_STATE ||
    @           state == VOTES_COUNTED_STATE ||
    @           state == REPORT_GENERATED_STATE;
  */

  /*@ constraint state == INIT_STATE ||
    @            state == \old(state) ||
    @            state == \old(state) + 1;
  */

  /** GUI stuff. */
  /*@ non_null */ JButton restartButton,
                          clearButton,
                          importCandidatesButton,
                          importVotesButton,
                          importPrivateKeyButton,
                          importPublicKeyButton,
                          decryptButton,
                          countButton,
                          reportButton,
                          helpButton,
                          exitButton; //@ in objectState;

  /** The (raw, imported) votes. */
  /*@ spec_public @*/ ArrayList rawVotes; //@ in objectState;

  /*@ invariant
    @    (state >= VOTES_IMPORTED_STATE ==> rawVotes != null);
  */

  /** The counted votes. */
  /*@ spec_public */ VoteSet voteSet; //@ in objectState;

  /*@ invariant
    @    (state >= VOTES_COUNTED_STATE ==> voteSet != null);
  */

  /** The candidates. */
  /*@ spec_public */ CandidateList candidates; //@ in objectState;

  /*@ invariant
    @    (state >= CANDIDATES_IMPORTED_STATE ==> candidates != null);
  */

  /** Private RSA key to decode the votes. */
  /*@ spec_public */ PrivateKey privateKey; //@ in objectState;

  /*@ invariant
    @    (state >= PRIVATE_KEY_IMPORTED_STATE ==> privateKey != null);
  */

  /** Public key. */
  /*@ spec_public */ PublicKey publicKey;  //@ in objectState;

  /*@ invariant
    @    (state >= PUBLIC_KEY_IMPORTED_STATE ==> publicKey != null);
  */

  /** The current directory used in file browser pop-ups. */
  /*@ spec_public non_null */ File currentDir; //@ in objectState;

  /** The help window. */
  /*@ non_null */ HelpAdapter helpAdapter; //@ in objectState;

  /**
   * Constructs a menu panel.
   * Don't use this constructor, use <code>getTheMenuPanel</code> instead.
   */
  /*@ private normal_behavior
    @    assignable objectState;
    @    ensures state == INIT_STATE;
    @*/
  private MenuPanel() {

    candidates = null;
    currentDir = new File(".");

    /* Build GUI... */

    restartButton = new JButton(RESTART_BUT_TXT);
    clearButton = new JButton(CLEAR_BUT_TXT);
    importCandidatesButton = new JButton(IMPORT_CANDIDATES_BUT_TXT);
    importVotesButton = new JButton(IMPORT_VOTES_BUT_TXT);
    importPrivateKeyButton = new JButton(IMPORT_PRIVATE_KEY_BUT_TXT);
    importPublicKeyButton = new JButton(IMPORT_PUBLIC_KEY_BUT_TXT);
    decryptButton = new JButton(DECRYPT_BUT_TXT);
    countButton = new JButton(COUNT_BUT_TXT);
    reportButton = new JButton(REPORT_BUT_TXT);
    helpButton = new JButton(HELP_BUT_TXT);
    exitButton = new JButton(EXIT_BUT_TXT);

    JPanel panel = new JPanel(new GridLayout(10,1));
    panel.add(restartButton);
    panel.add(clearButton);
    panel.add(importCandidatesButton);
    panel.add(importVotesButton);
    panel.add(importPrivateKeyButton);
    panel.add(importPublicKeyButton);
    panel.add(decryptButton);
    panel.add(countButton);
    panel.add(reportButton);
    panel.add(exitButton);
    add(panel,BorderLayout.CENTER);

    helpAdapter = new HelpAdapter();
    helpButton.addActionListener(helpAdapter);
    add(helpButton);

    setState(INIT_STATE);

    restartButton.addActionListener(new RestartAdapter());
    clearButton.addActionListener(new ClearAdapter());
    importCandidatesButton.addActionListener(new ImportCandidatesAdapter());
    importVotesButton.addActionListener(new ImportVotesAdapter());
    importPrivateKeyButton.addActionListener(new ImportKeyAdapter(PRIVATE_KEYTYPE));
    importPublicKeyButton.addActionListener(new ImportKeyAdapter(PUBLIC_KEYTYPE));
    decryptButton.addActionListener(new DecryptAdapter());
    countButton.addActionListener(new CountAdapter());
    reportButton.addActionListener(new ReportAdapter());
    exitButton.addActionListener(new ExitAdapter());
  }

  /**
   * Static factory method to get the menu panel instance.
   * This enforces the singleton property.
   *
   * @return the menu panel instance.
   */
  /*@ public behavior
    @    ensures \result == theInstance;
   */
  public static /*@ pure non_null */ MenuPanel getTheMenuPanel() {
    return theInstance;
  }

  /**
   * Sets the candidate list.
   *
   * @param candidates the new candidate list.
   */
  /*@ normal_behavior
    @    requires candidates != null;
    @    modifies this.candidates;
    @    ensures state == \old(state);
  */
  public void setCandidateList(CandidateList candidates) {
    this.candidates = candidates;
  }

  /**
   * Gets the candidate list.
   *
   * @return the candidate list.
   */
  /*@ normal_behavior
    @   ensures state == \old(state);
    @*/
  /*@ pure @*/ public CandidateList getCandidateList() {
    return candidates;
  }

  /**
   * Gets the raw votes list. The raw votes list contains byte arrays
   * representing encrypted votes, and strings representing unencrypted
   * votes.
   *
   * @return the raw voteslist.
   */
  /*@ normal_behavior
    @   ensures state == \old(state);
    @   ensures \result == rawVotes;
    @*/
  /*@ pure @*/ public ArrayList getRawVotes() {
    return rawVotes;
  }

  /**
   * Sets the raw votes list. The raw votes list contains byte arrays
   * representing encrypted votes, and strings representing unencrypted
   * votes.
   *
   * @param rawVotes the new raw votes list.
   */
  /*@ normal_behavior
    @   modifies this.rawVotes;
    @   ensures this.rawVotes.equals(rawVotes);
    @*/
  public void setRawVotes(/*@ non_null */ ArrayList rawVotes) {
    this.rawVotes = rawVotes;
  }

  /**
   * Gets the vote set. The vote set contains counted votes.
   *
   * @return the vote set.
   */
  /*@ normal_behavior
    @   ensures \result.equals(voteSet);
    @*/
  /*@ pure @*/ public VoteSet getVoteSet() {
    return voteSet;
  }

  /**
   * Sets the vote set. The vote set contains counted votes.
   *
   * @param voteSet the new vote set.
   */
  /*@ normal_behavior
    @   modifies this.voteSet;
    @   ensures this.rawVotes.equals(rawVotes);
    @*/
  public void setVoteSet(VoteSet voteSet) {
    this.voteSet = voteSet;
  }

  /**
   * Sets the private key.
   *
   * @param privateKey the new private key.
   */
  /*@ normal_behavior
    @   requires privateKey != null;
    @   modifies this.privateKey;
    @   ensures this.privateKey.equals(privateKey);
    @*/
  public void setPrivateKey(PrivateKey privateKey) {
    this.privateKey = privateKey;
  }

  /**
   * Sets the public key.
   *
   * @param publicKey the new public key.
   */
  /*@ normal_behavior
    @   requires publicKey != null;
    @   modifies this.publicKey;
    @   ensures this.publicKey.equals(publicKey);
    @*/
  public void setPublicKey(PublicKey publicKey) {
    this.publicKey = publicKey;
  }

  /**
   * Gets the imported private key or <code>null</code> if the key has not
   * been imported yet.
   *
   * @return the imported private key.
   */
  /*@ normal_behavior
    @    requires state >= PRIVATE_KEY_IMPORTED_STATE;
    @    ensures state == \old(state);
   */
  /*@ pure non_null @*/ public PrivateKey getPrivateKey() {
    return privateKey;
  }

  /**
   * Gets the imported public key or <code>null</code> if the key has not
   * been imported yet.
   *
   * @return the imported public key.
   */
  /*@ normal_behavior
    @    requires state >= PUBLIC_KEY_IMPORTED_STATE;
    @    ensures state == \old(state);
  */
  /*@ pure non_null @*/ public PublicKey getPublicKey() {
    return publicKey;
  }

  /**
   * Gets the current state.
   *
   * @return the current state.
   */
  /*@ normal_behavior
    @    ensures \result == state;
  */
  public /*@ pure @*/ int getState() {
    return state;
  }

  /**
   * Sets the state to <code>state</code>.
   * This automatically changes the GUI to reflect the change in state.
   *
   * @param state the new state.
   */
  /*@ normal_behavior
    @    requires state == INIT_STATE ||
    @             state == CLEARED_STATE ||
    @             state == CANDIDATES_IMPORTED_STATE ||
    @             state == VOTES_IMPORTED_STATE ||
    @             state == PRIVATE_KEY_IMPORTED_STATE ||
    @             state == PUBLIC_KEY_IMPORTED_STATE ||
    @             state == VOTES_DECRYPTED_STATE ||
    @             state == VOTES_COUNTED_STATE ||
    @             state == REPORT_GENERATED_STATE;
    @    modifies objectState;
    @    ensures this.state == state;
  */
  public void setState(int state) {
    this.state = state;
    helpAdapter.setText(state);
    setEnabled(true);
  }

  /**
   * Enables/disables the GUI.
   * When enabling, the GUI only enables those buttons that are
   * allowed in the current state.
   * When disabling, the GUI disables all buttons.
   *
   * @param b a boolean indicating whether to enable or disable the GUI.
   */
  /*@ also
    @ normal_behavior
    @   modifies objectState;
    @   ensures state == \old(state);
    @*/
  public void setEnabled(boolean b) {
    JRootPane rootPane = getRootPane();
    if (!b) {
      setEnabled(false,false,false,false,false,
                 false,false,false,false,false);
      rootPane.setDefaultButton(restartButton);
    } else {
      switch (state) {
      case INIT_STATE:
        setEnabled(true,true,false,false,false,
                   false,false,false,false,true);
        if (rootPane != null) {
           rootPane.setDefaultButton(clearButton);
        }
        clearButton.grabFocus();
        break;
      case CLEARED_STATE:
        setEnabled(true,false,true,false,false,
                   false,false,false,false,true);
        if (rootPane != null) {
           rootPane.setDefaultButton(importCandidatesButton);
        }
        importCandidatesButton.grabFocus();
        break;
      case CANDIDATES_IMPORTED_STATE:
        setEnabled(true,false,false,true,false,
                   false,false,false,false,true);
        if (rootPane != null) {
           rootPane.setDefaultButton(importVotesButton);
        }
        importVotesButton.grabFocus();
        break;
      case VOTES_IMPORTED_STATE:
        setEnabled(true,false,false,false,true,
                   false,false,false,false,true);
        if (rootPane != null) {
           rootPane.setDefaultButton(importPrivateKeyButton);
        }
        importPrivateKeyButton.grabFocus();
        break;
      case PRIVATE_KEY_IMPORTED_STATE:
        setEnabled(true,false,false,false,false,
                   true,false,false,false,true);
        if (rootPane != null) {
           rootPane.setDefaultButton(importPublicKeyButton);
        }
        importPublicKeyButton.grabFocus();
        break;
      case PUBLIC_KEY_IMPORTED_STATE:
        setEnabled(true,false,false,false,false,
                   false,true,false,false,true);
        if (rootPane != null) {
           rootPane.setDefaultButton(decryptButton);
        }
        decryptButton.grabFocus();
        break;
      case VOTES_DECRYPTED_STATE:
        setEnabled(true,false,false,false,false,
                   false,false,true,false,true);
        if (rootPane != null) {
           rootPane.setDefaultButton(countButton);
        }
        countButton.grabFocus();
        break;
      case VOTES_COUNTED_STATE:
      case REPORT_GENERATED_STATE:
        setEnabled(true,false,false,false,false,
                   false,false,false,true,true);
        if (rootPane != null) {
           rootPane.setDefaultButton(reportButton);
        }
        reportButton.grabFocus();
        break;
      }
    }
  }

  /**
   * Enables/disables the 10 task buttons of the GUI.
   *
   * @param b0 a boolean indicating whether to enable or disable button 1.
   * @param b1 a boolean indicating whether to enable or disable button 2.
   * @param b2 a boolean indicating whether to enable or disable button 3.
   * @param b3 a boolean indicating whether to enable or disable button 4.
   * @param b4 a boolean indicating whether to enable or disable button 5.
   * @param b5 a boolean indicating whether to enable or disable button 6.
   * @param b6 a boolean indicating whether to enable or disable button 7.
   * @param b7 a boolean indicating whether to enable or disable button 8.
   * @param b8 a boolean indicating whether to enable or disable button 9.
   * @param b9 a boolean indicating whether to enable or disable button 10.
   */
  /*@ private normal_behavior
    @   modifies objectState;
    @    ensures state == \old(state);
    @*/
  private void setEnabled(boolean b0, boolean b1, boolean b2, boolean b3,
                          boolean b4, boolean b5, boolean b6, boolean b7,
                          boolean b8, boolean b9) {
    restartButton.setEnabled(b0);
    clearButton.setEnabled(b1);
    importCandidatesButton.setEnabled(b2);
    importVotesButton.setEnabled(b3);
    importPrivateKeyButton.setEnabled(b4);
    importPublicKeyButton.setEnabled(b5);
    decryptButton.setEnabled(b6);
    countButton.setEnabled(b7);
    reportButton.setEnabled(b8);
    exitButton.setEnabled(b9);
  }

  /**
   * Sets the current directory used in file browser pop-ups.
   *
   * @param currentDir the new current directory.
   */
  /*@ behavior
    @    assignable this.currentDir;
    @    ensures this.currentDir.equals(currentDir);
    @    ensures state == \old(state);
   */
  void setCurrentDir(/*@ non_null */ File currentDir) {
    this.currentDir = currentDir;
  }

  /**
   * Gets the current directory used in file browser pop-ups.
   *
   * @return the current directory.
   */
  /*@ behavior
    @    ensures \result.equals(currentDir);
   */
  /*@ pure non_null */ File getCurrentDir() {
    return currentDir;
  }

  /**
   * Adds an action listener to the exit button.
   *
   * @param l the action listener.
   */
  /*@ normal_behavior
    @    modifies objectState;
    @    ensures state == \old(state);
    @*/
  public void addExitButtonListener(ActionListener l) {
    exitButton.addActionListener(l);
  }
 
  /**
   * Clears the list of candidates, the keys, the raw votes,
   *  and the counted votes.
   */
  /*@ normal_behavior
    @   modifies objectState;
    @   ensures candidates == null;
    @   ensures rawVotes == null;
    @   ensures voteSet == null;
    @   ensures privateKey == null;
    @   ensures publicKey == null;
    @*/
  public void clear() {
    if (candidates != null) {
       candidates.clear();
       candidates = null;
    }
    rawVotes = null;
    voteSet = null;
    privateKey = null;
    publicKey = null;
  }

  /**
   * Main method creates frame and calls constructor.
   *
   * @param arg the command line arguments.
   */
  public static void main(String[] arg) {
    MenuPanel mp = getTheMenuPanel();
    JFrame frame = new JFrame(TITLE);
    Container c = frame.getContentPane();
    c.add(mp);
    frame.addWindowListener(new ExitAdapter());
    frame.pack();
    frame.setVisible(true);
  }
}

