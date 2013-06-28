/*
 * JML specification Copyright 2004 SoS Group, University of Nijmegen
 */

package sos.koa;

import java.util.Set;
import java.util.Iterator;
/**
 * The set of votes in an election.
 *
 * @author Joe Kiniry (kiniry@cs.kun.nl)
 * @version $Id: VoteSet.java,v 1.31 2004/05/29 17:39:57 hubbers Exp $
 */

public class VoteSet
  implements java.io.Serializable
{
  /**
   * A flag that indicates that the vote has been initialized and the only
   * thing happening henceforth is counting then finalizing.
   */
  private /*@ spec_public @*/ boolean my_vote_has_been_initialized; //@ in objectState;

  /**
   * A flag that indicates that the vote has been finalized and the only
   * thing happening henceforth is requesting the total count.
   */
  private /*@ spec_public @*/ boolean my_vote_has_been_finalized; //@ in objectState;
  //@ invariant my_vote_has_been_finalized ==> my_vote_has_been_initialized;

  /**
   * The list of all candidates in an election.
   */
  private /*@ non_null spec_public @*/ CandidateList my_candidate_list; //@ in objectState;
  //@ invariant my_candidate_list.owner == this;


  /**
   * Constructs a new, initialized VoteSet for the provided CandidateList.
   *
   * @param a_candidate_list the CandidateList to be used in the vote.
   *
   * <pre><jml>
   * normal_behavior
   *   ensures my_candidate_list == a_candidate_list;
   *   ensures !my_vote_has_been_initialized && !my_vote_has_been_finalized;
   * </jml></pre>
   */
  /*@ pure @*/ VoteSet(final /*@ non_null @*/ CandidateList a_candidate_list) {
    my_candidate_list = a_candidate_list;
    //@ set my_candidate_list.owner = this;
  }

  /**
   * Validate the information provided, which are the redundant
   * components of an encrypted vote.  Validation means that the given
   * position number corresponds to the candidate who has all of the
   * other provided information.
   *
   * @param a_candidate_code the candidate's code.
   * @param a_lastname the candidate's lastname.
   * @param some_initials the candidate's initials.
   * @param a_party_name the candidate's party name.
   * @param a_party_number the candidate's party number.
   * @param a_position_number the candidate's position number.
   * @return a flag indicating the validity of the provided data.
   * @exception IllegalArgumentException is thrown if the vote has not been
   * initialized or the vote has already been finalized.
   * @see #initializeVote()
   * @see #finalizeVote()
   *
   *
   * <pre><jml>
   * normal_behavior
   *   requires my_vote_has_been_initialized && !my_vote_has_been_finalized;
   *   requires (* all parameters must be of the proper length *);
   *   requires a_lastname.length() <= Candidate.LASTNAME_MAX_LENGTH;
   *   requires some_initials.length() <= Candidate.INITIALS_MAX_LENGTH;
   *   requires a_position_number.length() <= Candidate.POSITION_NUMBER_MAX_LENGTH;
   *   requires a_party_name.length() <= KiesKring.KIESKRING_NAME_MAX_LENGTH;
   *   requires 0 <= Byte.parseByte(a_party_number);
   *   requires Byte.parseByte(a_party_number) <= CandidateList.MAX_KIESKRINGEN_PER_CANDIDATE_LIST;
   *   requires 0 <= Byte.parseByte(a_position_number);
   *   requires Byte.parseByte(a_position_number) <= KiesLijst.MAX_CANDIDATES_PER_KIESLIJST;
   *   requires my_candidate_list.validCandidate(a_candidate_code);
   *   ensures \result ==> my_candidate_list.getCandidate(a_candidate_code) != null;
   *   ensures \result ==> my_candidate_list.getCandidate(a_candidate_code).lastname().equals(a_lastname);
   *   ensures \result ==> my_candidate_list.getCandidate(a_candidate_code).initials().equals(some_initials);
   *   ensures \result ==> my_candidate_list.getCandidate(a_candidate_code).kiesLijst().name().equals(a_party_name);
   *   ensures \result ==> my_candidate_list.getCandidate(a_candidate_code).kiesLijst().number() == Byte.parseByte(a_party_number);
   *   ensures \result <== (my_candidate_list.getCandidate(a_candidate_code) != null &&
   *                       my_candidate_list.getCandidate(a_candidate_code).lastname().equals(a_lastname) &&
   *                       my_candidate_list.getCandidate(a_candidate_code).initials().equals(some_initials) &&
   *                       my_candidate_list.getCandidate(a_candidate_code).kiesLijst().name().equals(a_party_name) &&
   *                       my_candidate_list.getCandidate(a_candidate_code).kiesLijst().number() == Byte.parseByte(a_party_number));
   * also
   * exceptional_behavior
   *   requires !(my_vote_has_been_initialized && !my_vote_has_been_finalized);
   *   signals (IllegalArgumentException) true;
   * </jml></pre>
   */
  final /*@ pure @*/ boolean
    validateRedundantInfo(final /*@ non_null @*/ String a_candidate_code,
                          final /*@ non_null @*/ String a_lastname,
                          final /*@ non_null @*/ String some_initials,
                          final /*@ non_null @*/ String a_party_name,
                          final /*@ non_null @*/ String a_party_number,
                          final /*@ non_null @*/ String a_position_number)
                          throws KOAException {
    if (!(my_vote_has_been_initialized && !my_vote_has_been_finalized)) {
      throw new IllegalArgumentException();
    }

    final Candidate candidate = my_candidate_list.getCandidate(a_candidate_code);
    assert (candidate != null);
    return candidate.lastname().equals(a_lastname) &&
      candidate.initials().equals(some_initials) &&
      candidate.position_number() == Byte.parseByte(a_position_number) &&
      candidate.kiesLijst().name().equals(a_party_name) &&
      candidate.kiesLijst().number() == Byte.parseByte(a_party_number);
  }

  /**
   * Validate the information provided, which are the redundant
   * components of an encrypted vote.  Validation means that the
   * kieskring represented by the given kieskring number contains
   * the specified candidate code.
   *
   * @param a_candidate_code the code of the candidate to validate
   * @param a_kieskring_number the number of the kieskring to validate.
   * @return a flag indicating the validity of the provided data.
   * @exception IllegalArgumentException is thrown if the vote has not been
   * initialized or the vote has already been finalized.
   * @see #initializeVote()
   * @see #finalizeVote()
   *
   *
   * <pre><jml>
   * normal_behavior
   *   requires my_vote_has_been_initialized && !my_vote_has_been_finalized;
   *   requires 0 <= Byte.parseByte(a_kieskring_number);
   *   requires Byte.parseByte(a_kieskring_number) <= CandidateList.MAX_KIESKRINGEN_PER_CANDIDATE_LIST;
   *   requires my_candidate_list.validCandidate(a_candidate_code);
   *   ensures \result ==> my_candidate_list.getCandidate(a_candidate_code) != null;
   *   ensures \result ==> my_candidate_list.getCandidate(a_candidate_code).kiesKring().number() == Byte.parseByte(a_kieskring_number);
   *   ensures \result ==> AuditLog.hasKiesKring(my_candidate_list.getCandidate(a_candidate_code).kiesKring().number());
   *   ensures \result <== (my_candidate_list.getCandidate(a_candidate_code) != null &&
   *                        my_candidate_list.getCandidate(a_candidate_code).kiesKring().number() == Byte.parseByte(a_kieskring_number) &&
   *                        AuditLog.hasKiesKring(my_candidate_list.getCandidate(a_candidate_code).kiesKring().number())
   *                       );
   * also
   * exceptional_behavior
   *   requires !(my_vote_has_been_initialized && !my_vote_has_been_finalized);
   *   signals (IllegalArgumentException) true;
   * </jml></pre>
   */
  final /*@ pure @*/ boolean
    validateKiesKringNumber(final /*@ non_null @*/ String a_candidate_code,
                            final /*@ non_null @*/ String a_kieskring_number) {
    if (!(my_vote_has_been_initialized && !my_vote_has_been_finalized)) {
      throw new IllegalArgumentException();
    }

    final Candidate candidate = my_candidate_list.getCandidate(a_candidate_code);
    assert candidate != null;
    return candidate.kiesKring().number() == Byte.parseByte(a_kieskring_number) &&
      AuditLog.hasKiesKring(candidate.kiesKring().number());

  }

  /**
   * @return a flag indicating if the specified candidate code is a valid
   * candidate for this vote set.
   *
   * @param a_candidate_code the candidate code to check.
   *
   * <pre><jml>
   * normal_behavior
   *   requires 0 <= Integer.parseInt(a_candidate_code);
   *   ensures \result == my_candidate_list.validCandidate(a_candidate_code);
   * </jml></pre>
   */
  final /*@ pure @*/ boolean validCandidate(final /*@ non_null @*/ String a_candidate_code) {
    return my_candidate_list.validCandidate(a_candidate_code);
  }

  /**
   * @return a flag indicating if the specified candidate code is a valid
   * candidate for this vote set.
   *
   * @param a_candidate_code the candidate code to check.
   *
   * <pre><jml>
   * normal_behavior
   *   requires 0 <= a_candidate_code;
   *   ensures \result == my_candidate_list.validCandidate(a_candidate_code);
   * </jml></pre>
   */
  final /*@ pure @*/ boolean validCandidate(final int a_candidate_code) {
    return my_candidate_list.validCandidate(a_candidate_code);
  }

  /**
   * Initialize the vote for this vote set.  Initialization may only
   * happen once.  After initialization, the only methods that may be
   * called are those whose preconditions are
   * <code>my_vote_has_been_initialized</code>.
   *
   * @exception IllegalArgumentException is thrown if the vote has not been
   * initialized or the vote has already been finalized.
   * @see #finalizeVote()
   *
   * <pre><jml>
   * normal_behavior
   *   requires !my_vote_has_been_initialized && !my_vote_has_been_finalized;
   *   assignable my_vote_has_been_initialized;
   *   ensures my_vote_has_been_initialized;
   * also
   * exceptional_behavior
   *   requires my_vote_has_been_initialized || my_vote_has_been_finalized;
   *   assignable \nothing;
   *   signals (IllegalArgumentException) true;
   * </jml></pre>
   */
  final void initializeVote() {
    if (my_vote_has_been_initialized || my_vote_has_been_finalized) {
      throw new IllegalArgumentException();
    }

    my_vote_has_been_initialized = true;
  }

  /**
   * Add a single vote to this vote set for the specified candidate
   * code.
   *
   * @param a_candidate_code the candidate code for which to increment
   * the vote count by one.
   * @exception IllegalArgumentException is thrown if the vote has not been
   * initialized or the vote has already been finalized.
   *
   * <pre><jml>
   * normal_behavior
   *   requires my_vote_has_been_initialized;
   *   requires !my_vote_has_been_finalized;
   *   requires 0 <= Integer.parseInt(a_candidate_code);
   *   requires validCandidate(a_candidate_code);
   *   assignable \everything;
   *   ensures my_candidate_list.getCandidate(a_candidate_code).voteCount() ==
   *           \old(my_candidate_list.getCandidate(a_candidate_code).voteCount() + 1);
   *   ensures my_candidate_list.getCandidate(a_candidate_code).kiesLijst().voteCount() ==
   *           \old(my_candidate_list.getCandidate(a_candidate_code).kiesLijst().voteCount() + 1);
   * also
   * exceptional_behavior
   *   requires !(my_vote_has_been_initialized &&
   *              !my_vote_has_been_finalized &&
   *              0 <= Integer.parseInt(a_candidate_code) &&
   *              validCandidate(a_candidate_code));
   *   assignable \nothing;
   *   signals (IllegalArgumentException) true;
   * </jml></pre>
   */
  final void addVote(final /*@ non_null @*/ String a_candidate_code) {
    if (!(my_vote_has_been_initialized &&
          !my_vote_has_been_finalized) &&
          0 <= Integer.parseInt(a_candidate_code) &&
          validCandidate(a_candidate_code)) {
      throw new IllegalArgumentException();
    }

    final Candidate candidate = my_candidate_list.getCandidate(a_candidate_code);
    assert (candidate != null);
    candidate.incrementVoteCount();
    candidate.kiesLijst().incrementVoteCount();
  }

  /**
   * Add a single vote to this vote set for the specified candidate
   * code.
   *
   * @param a_candidate_code the candidate code for which to increment
   * the vote count by one.
   * @exception IllegalArgumentException is thrown if the vote has not been
   * initialized or the vote has already been finalized.
   *
   * <pre><jml>
   * normal_behavior
   *   requires my_vote_has_been_initialized && !my_vote_has_been_finalized;
   *   requires 0 <= a_candidate_code;
   *   requires validCandidate(a_candidate_code);
   *   assignable \everything;
   *   ensures my_candidate_list.getCandidate(a_candidate_code).voteCount() ==
   *           \old(my_candidate_list.getCandidate(a_candidate_code).voteCount() + 1);
   * also
   * exceptional_behavior
   *   requires !(my_vote_has_been_initialized && !my_vote_has_been_finalized);
   *   assignable \nothing;
   *   signals (IllegalArgumentException) true;
   * </jml></pre>
   */
  final void addVote(final int a_candidate_code) {
    if (!(my_vote_has_been_initialized && !my_vote_has_been_finalized)) {
      throw new IllegalArgumentException();
    }

    final Candidate candidate = my_candidate_list.getCandidate(a_candidate_code);
    assert candidate != null;
    candidate.incrementVoteCount();
    candidate.kiesLijst().incrementVoteCount();
  }

  /**
   * Finalize the vote for this vote set.  Finalization may only
   * happen once.  After finalization, the only methods that may be
   * called are those whose preconditions are
   * <code>my_vote_has_been_finalized</code>.  Finalizing the vote
   * means that no more votes are to be counted.
   *
   * @exception IllegalArgumentException is thrown if the vote has not been
   * initialized or the vote has already been finalized.
   * @see #initializeVote()
   *
   * <pre><jml>
   * normal_behavior
   *   requires my_vote_has_been_initialized && !my_vote_has_been_finalized;
   *   assignable my_vote_has_been_finalized;
   *   ensures my_vote_has_been_finalized;
   * also
   * exceptional_behavior
   *   requires !(my_vote_has_been_initialized && !my_vote_has_been_finalized);
   *   assignable \nothing;
   *   signals (IllegalArgumentException) true;
   * </jml></pre>
   */
  final void finalizeVote() {
    if (!(my_vote_has_been_initialized && !my_vote_has_been_finalized)) {
      throw new IllegalArgumentException();
    }
    my_vote_has_been_finalized = true;
  }

  /**
   * @return the number of votes cast for the specified candidate code.
   *
   * @param a_candidate_code the candidate code of interest.
   * @exception IllegalArgumentException is thrown if the vote has not been
   * initialized and the vote has note been finalized.
   *
   * <pre><jml>
   * normal_behavior
   *   requires my_vote_has_been_initialized && my_vote_has_been_finalized;
   *   requires 0 <= Integer.parseInt(a_candidate_code);
   *   requires validCandidate(a_candidate_code);
   *   ensures 0 <= \result;
   * also
   * exceptional_behavior
   *   requires !(my_vote_has_been_initialized && my_vote_has_been_finalized);
   *   signals (IllegalArgumentException) true;
   * </jml></pre>
   */
  final /*@ pure @*/ int voteCount(final /*@ non_null @*/ String a_candidate_code) {
    if (!(my_vote_has_been_initialized && my_vote_has_been_finalized)) {
      throw new IllegalArgumentException();
    }
    final Candidate candidate = my_candidate_list.getCandidate(a_candidate_code);
    return candidate.voteCount();
  }

  /**
   * @return the number of votes cast for the specified candidate code.
   *
   * @param a_candidate_code the candidate code of interest.
   * @exception IllegalArgumentException is thrown if the vote has not been
   * initialized and the vote has note been finalized.
   *
   * <pre><jml>
   * normal_behavior
   *   requires my_vote_has_been_initialized && my_vote_has_been_finalized;
   *   requires 0 <= a_candidate_code;
   *   requires validCandidate(a_candidate_code);
   *   ensures 0 <= \result;
   * also
   * exceptional_behavior
   *   requires !(my_vote_has_been_initialized && my_vote_has_been_finalized);
   *   signals (IllegalArgumentException) true;
   * </jml></pre>
   */
  final /*@ pure @*/ int voteCount(final int a_candidate_code) {
    if (!(my_vote_has_been_initialized && my_vote_has_been_finalized)) {
      throw new IllegalArgumentException();
    }
    final Candidate candidate = my_candidate_list.getCandidate(a_candidate_code);
    return candidate.voteCount();
  }

  /*@
    @ assignable my_candidate_list.*;
    @*/ 
  final void resetVotes() {
    int j,k;
    Set orderedKiesKringen = my_candidate_list.getKiesKringen().keySet(); 
    assert (orderedKiesKringen != null);
    Iterator i = orderedKiesKringen.iterator();
    assert (i != null);   
    while (i.hasNext()) {
      Byte b = (Byte)(i.next());
      KiesKring kiesKring = (KiesKring)(my_candidate_list.getKiesKringen().get(b));

      for (j = 0; j < kiesKring.my_kiesLijsten.length; j++) {
        KiesLijst kiesLijst = kiesKring.my_kiesLijsten[j];     
        if (kiesLijst != null) {
          for (k = 0; k < kiesLijst.my_candidates.length; k++) {
            Candidate candidate = kiesLijst.my_candidates[k];
            if (candidate != null) {
              candidate.resetVoteCount();
            }
          }
          kiesLijst.resetVoteCount();
        }
      }
    }
  }
}
