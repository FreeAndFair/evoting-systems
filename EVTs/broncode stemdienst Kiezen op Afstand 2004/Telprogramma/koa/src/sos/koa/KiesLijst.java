/*
 * JML specification Copyright 2004 SoS Group, University of Nijmegen
 */

package sos.koa;

/**
 * A kieslijst in an election.
 *
 * @author Joe Kiniry (kiniry@cs.kun.nl)
 * @version $Id: KiesLijst.java,v 1.30 2004/05/28 20:37:23 hubbers Exp $
 */

final class KiesLijst
  implements Comparable, java.io.Serializable
{
  /**
   * The "Blanco" kieslijst is hard-coded, according to the Ministry,
   * as 99.
   */
  static final byte BLANCO = 99;

  /**
   * The maximum length, in digits represented by characters, of a
   * kieslijst's number (kieslijstnummer).
   *
   * @design As specified by the LogicaCMG specification, the
   * kieslijstnummber in the stemmen file is encoded as char[2], thus
   * its maximum length is 2.
   */
  static final byte KIESLIJST_NUMBER_MAX_LENGTH = 2;

  /**
   * The maximum length in characters of a groepering's name.
   *
   * @design Not specified by the LogicaCMG documentation, but given by
   * the ministry directly.
   */
  static final byte GROEPERING_NAME_MAX_LENGTH = 80;

  /**
   * The maximum number of candidates per kieslijst, by law.
   */
  //@ invariant (* MAX_CANDIDATES_PER_KIESLIJST == 80 by law *);
  static final byte MAX_CANDIDATES_PER_KIESLIJST = 80;
  //@ invariant 0 <= candidateCount() && candidateCount() <= MAX_CANDIDATES_PER_KIESLIJST;

  /**
   * A cache of all kieslijsts ever constructed.  This cache is used by the
   * factory method <code>make()</code>.
   *
   * @see #make(byte, byte, java.lang.String)
   */
  private static final /*@ non_null spec_public @*/ KiesLijst[] MY_CACHED_KIESLIJSTEN =
    new KiesLijst[CandidateList.MAX_KIESKRINGEN_PER_CANDIDATE_LIST *
                  (KiesKring.MAX_KIESLIJSTEN_PER_KIESKRING + 1) + 1];
  //@ invariant (\forall int i; 0 <= i && i < MY_CACHED_KIESLIJSTEN.length; MY_CACHED_KIESLIJSTEN[i].owner == MY_CACHED_KIESLIJSTEN);

  /**
   * The candidates in this kieslijst.
   *
   * @design Since we use the position number as index, it runs from 1
   * till MAX_CANDIDATES_PER_KIESLIJST instead of from 0 till
   * MAX_CANDIDATES_PER_KIESLIJST - 1.  Thus, this invariant's odd
   * "+1" on the end.
   */
  /* private */ final /*@ non_null spec_public @*/ Candidate[] my_candidates =
    new Candidate [MAX_CANDIDATES_PER_KIESLIJST + 1]; //@ in objectState;
  //@ invariant my_candidates.length == MAX_CANDIDATES_PER_KIESLIJST + 1;
  //@ invariant (\forall int i; 0 <= i && i < my_candidates.length; my_candidates[i].owner == this);

  /**
   * This number (kieslijstnummer) of this kieslijst.
   *
   */
  private /*@ spec_public @*/ byte my_number; //@ in objectState;
  //@ invariant 0 <= my_number && my_number <= KiesKring.MAX_KIESLIJSTEN_PER_KIESKRING;

  /**
   * The name (kieslijstnaam) of this kieslijst.
   *
   */
  private /*@ non_null spec_public @*/ String my_name; //@ in objectState;
  //@ invariant my_name.length() <= GROEPERING_NAME_MAX_LENGTH;
  //@ invariant my_name.owner == this;

  /**
   * The number of the kieskring in which this kieslijst resides.
   */
  private /*@ spec_public @*/ byte my_kieskring_number; //@ in objectState;
  //@ invariant 0 <= my_kieskring_number;
  //@ invariant my_kieskring_number <= CandidateList.MAX_KIESKRINGEN_PER_CANDIDATE_LIST;

  /**
   * The number of candidates in this kieslijst.
   */
  private /*@ spec_public @*/ byte my_candidate_count; //@ in objectState;
  //@ invariant 0 <= my_candidate_count;
  //@ invariant my_candidate_count <= MAX_CANDIDATES_PER_KIESLIJST;

  /**
   * The total number of votes counted in this kieslijst.
   */
  private /*@ spec_public @*/ int my_vote_count; //@ in objectState;
  //@ invariant my_vote_count >= 0;
  // Because AuditLog.setCountNrOfVotes() is not called yet we can
  // only compare with AuditLog.getDecryptNrOfVotes().
  //@ invariant my_vote_count <= AuditLog.getDecryptNrOfVotes();



  // Constructors

  /**
   * Construct a new kieslijst object given the specified
   * initialization values.
   *
   * @design This constructor is intentionally private; use the
   * factory method <code>make()</code> to obtain new kieslijst
   * objects instead.
   *
   * @see #make(byte, byte, java.lang.String)
   *
   * <pre><jml>
   * private normal_behavior
   *   requires 0 <= a_kieskring_number;
   *   requires a_kieskring_number <= CandidateList.MAX_KIESKRINGEN_PER_CANDIDATE_LIST;
   *   requires 0 <= a_number && a_number <= KiesKring.MAX_KIESLIJSTEN_PER_KIESKRING;
   *   requires a_name.length() <= GROEPERING_NAME_MAX_LENGTH;
   *   modifies objectState;
   *   ensures number() == a_number;
   *   ensures name().equals(a_name);
   *   ensures candidateCount() == 0;
   *   ensures my_kieskring_number == a_kieskring_number;
   * </jml></pre>
   */
  private KiesLijst(final byte a_kieskring_number,
                    final byte a_number,
                    final /*@ non_null @*/ String a_name) {
    my_kieskring_number = a_kieskring_number;
    my_number = a_number;
    my_name = a_name;
    my_candidate_count = 0;
    //@ set my_name.owner = this;
  }

  /**
   * This is the factory method for obtaining new kieslijst objects, given
   * the specified initialization values.
   *
   * @param a_kieskring_number the number of the kieskring in which this
   * kieslijst resides.
   * @param a_number the number of the new kieslijst.
   * @param a_name the name of the new kieslijst.
   * @return the kieslijst that represents the specified values.
   *
   * @design kiniry Apr 2004 - This method is not pure according to
   * the current definition of pure.  Since it has no visible
   * side-effects though, we can use it is specifications freely.
   *
   * <pre><jml>
   * private normal_behavior
   *   requires 0 <= a_kieskring_number;
   *   requires a_kieskring_number <= CandidateList.MAX_KIESKRINGEN_PER_CANDIDATE_LIST;
   *   requires 0 <= a_number && a_number <= KiesKring.MAX_KIESLIJSTEN_PER_KIESKRING;
   *   requires a_name.length() <= GROEPERING_NAME_MAX_LENGTH;
   *   ensures \result.number() == a_number;
   *   ensures \result.name().equals(a_name);
   *   ensures \result.candidateCount() >= 0;
   *   ensures MY_CACHED_KIESLIJSTEN[a_kieskring_number *
   *             KiesKring.MAX_KIESLIJSTEN_PER_KIESKRING + a_number] != null;
   * </jml></pre>
   */
  static /*@ pure @*/ KiesLijst make(final byte a_kieskring_number,
                                     final byte a_number,
                                     final /*@ non_null @*/ String a_name) {
    final int index = a_kieskring_number *
      KiesKring.MAX_KIESLIJSTEN_PER_KIESKRING + a_number;
    if (MY_CACHED_KIESLIJSTEN[index] != null) {
      if (MY_CACHED_KIESLIJSTEN[index].number() == a_number &&
          MY_CACHED_KIESLIJSTEN[index].name().equals(a_name)) {
        return MY_CACHED_KIESLIJSTEN[index];
      }
    }
    KiesLijst result = new KiesLijst(a_kieskring_number, a_number, a_name);
    //@ set result.owner = MY_CACHED_KIESLIJSTEN;
    MY_CACHED_KIESLIJSTEN[index] = result;
    return result;
  }


  // Accessors so that we can rely upon invariants and have pure data access.

  /**
   * @return the number of this kieslijst.
   *
   * <pre><jml>
   * normal_behavior
   *   ensures 0 <= \result && \result <= KiesKring.MAX_KIESLIJSTEN_PER_KIESKRING;
   *   ensures \result == my_number;
   * </jml></pre>
   */
  /*@ pure @*/ byte number() {
    return my_number;
  }

  /**
   * @return the name of this kieslijst.
   *
   * <pre><jml>
   * normal_behavior
   *   ensures \result.length() <= GROEPERING_NAME_MAX_LENGTH;
   *   ensures \result == my_name;
   * </jml></pre>
   */
  /*@ pure non_null @*/ String name() {
    return my_name;
  }

  /**
   * Add a candidate to this kieslijst.
   *
   * @param a_candidate the candidate to add.
   *
   * <pre><jml>
   * normal_behavior
   *   requires candidateCount() < KiesLijst.MAX_CANDIDATES_PER_KIESLIJST;
   *   modifies \everything;
   *   ensures candidates()[\old(a_candidate.position_number())] == a_candidate;
   *   ensures candidateCount() == \old(candidateCount() + 1);
   *   ensures candidateCount() <= KiesLijst.MAX_CANDIDATES_PER_KIESLIJST;
   * </jml></pre>
   */
  void addCandidate(final /*@ non_null @*/ Candidate a_candidate) {
    // @design We may assume that the input files are correct, so it 
    // shouldn't happen that the candidate is already in the array.
    assert (my_candidates[a_candidate.position_number()] == null);

    my_candidates[a_candidate.position_number()] =  a_candidate;
    my_candidate_count++;
    //@ set a_candidate.owner = this;
  }

  /**
   * @return the candidates of this kieslijst.
   *
   * <pre><jml>
   * normal_behavior
   *   ensures \result == my_candidates;
   * </jml></pre>
   */
  /*@ pure non_null @*/ Candidate[] candidates() {
    return my_candidates;
  }

  /**
   * @return the number of candidates in this kieslijst.
   *
   * <pre><jml>
   * normal_behavior
   *   ensures 0 <= \result && \result <= KiesLijst.MAX_CANDIDATES_PER_KIESLIJST;
   *   ensures \result == my_candidate_count;
   * </jml></pre>
   */
  /*@ pure @*/ byte candidateCount() {
    return my_candidate_count;
  }


  // Vote count

  /**
   * Increment the number of votes counted in this kieslijst by one.
   *
   * @return the total number of votes, including the one just added.
   *
   * <pre><jml>
   * normal_behavior
   *   requires my_vote_count < AuditLog.getDecryptNrOfVotes();
   *   modifies my_vote_count;
   *   ensures my_vote_count == \old(my_vote_count + 1);
   * </jml></pre>
   */
  int incrementVoteCount() {
    my_vote_count = my_vote_count + 1;
    return my_vote_count;
  }

  /**
   * @return the number of votes counted in this kieslijst.
   *
   * <pre><jml>
   * normal_behavior
   *   ensures \result == my_vote_count;
   * </jml></pre>
   */
  /*@ pure @*/ int voteCount() {
    return my_vote_count;
  }

  /**
   * Reset the number of votes counted in this kieslijst to zero.
   *
   * <pre><jml>
   * normal_behavior
   *   modifies my_vote_count;
   *   ensures my_vote_count == 0;
   * </jml></pre>
   */
  void resetVoteCount() {
    my_vote_count = 0;
  }

  /**
   * Clears all data in this <code>KiesLijst</code> instance. In
   * particular, all candidate references are cleared.
   *
   * <pre><jml>
   * normal_behavior
   *   modifies objectState;
   *
   *   ensures my_number == 0;
   *   ensures my_name.equals("");
   *   ensures my_kieskring_number == 0;
   *   ensures my_candidate_count == 0;
   *   ensures my_vote_count == 0;
   *
   *   ensures (\forall int i; i < my_candidates.length; my_candidates[i] == null);
   *   ensures (\forall int i; i < MY_CACHED_KIESLIJSTEN.length;
   *                           MY_CACHED_KIESLIJSTEN[i] == null);
   *
   *   ensures_redundantly number() == 0;
   *   ensures_redundantly name().equals("");
   *   ensures_redundantly voteCount() == 0;
   *   ensures_redundantly candidateCount() == 0;
   * </jml></pre>
   */
  void clear() {
    my_number = 0;
    my_name = "";
    my_kieskring_number = 0;
    my_candidate_count = 0;
    my_vote_count = 0;
    for (int i = 0; i < my_candidates.length; i++) {
      if (my_candidates[i] != null) {
        my_candidates[i] = null;
      }
    }
    for (int i = 0; i < MY_CACHED_KIESLIJSTEN.length; i++) {
      MY_CACHED_KIESLIJSTEN[i] = null;
    }
  }


  // Implementation of Object

  /** {@inheritDoc} */
  public boolean equals(final Object an_object) {
    if (an_object == null) {
      return false;
    }

    if (!(an_object instanceof KiesLijst)) {
      return false;
    }
    final KiesLijst k = (KiesLijst)an_object;

    return (k.number() == number()) &&
      k.name().equals(name()) &&
      k.candidates().equals(candidates());
  }

  /** {@inheritDoc} */
  public int hashCode() {
    return my_name.hashCode(); //@ nowarn Modifies;
  }

  /** {@inheritDoc} */
  public String toString() {
    Candidate cand;
    final StringBuffer result =
      new StringBuffer(number() + "." + (number() < 10 ? "  " : " ") + name() + "\n");
    for (int i = 0; i < KiesLijst.MAX_CANDIDATES_PER_KIESLIJST; i++) {
      // result.append(result + "candidate #" + i + ": " + candidates().get(i) + "\n");
      cand = candidates()[i];
      if (cand != null) {
        result.append(result + "candidate #" + i + ": " + cand.lastname() + "\n");
      }
    }
    return result.toString();
  }


  // Implementation of Comparable

  /** {@inheritDoc} */
  public int compareTo(final Object an_object) {
    if (!(an_object instanceof KiesKring)) {
      throw new ClassCastException();
    }

    final KiesKring k = (KiesKring) an_object;
    return number() - k.number();
  } //@ nowarn Exception, Post;
}
