/*
 * JML specification Copyright 2004 SoS Group, University of Nijmegen
 */

package sos.koa;

/**
 * The metadata associated with a candidiate list for an election.
 *
 * @author Joe Kiniry (kiniry@cs.kun.nl)
 * @version $Id: CandidateListMetadata.java,v 1.13 2004/05/28 20:37:23 hubbers Exp $
 */

class CandidateListMetadata
{
  /**
   * The request reference of the associated candidate list.
   */
  private /*@ non_null spec_public @*/ String my_requestReference; //@ in objectState;

  /**
   * The response reference of the associated candidate list.
   */
  private /*@ non_null spec_public @*/ String my_responseReference; //@ in objectState;

  /**
   * The creation time of the associated candidate list.
   */
  private /*@ non_null spec_public @*/ String my_creationTime; //@ in objectState;

  /**
   * The number of kieskringen in the associated candidate list.
   */
  private /*@ spec_public @*/ byte my_kiesKringCount; //@ in objectState;
  //@ invariant 0 <= my_kiesKringCount;
  //@ invariant my_kiesKringCount <= CandidateList.MAX_KIESKRINGEN_PER_CANDIDATE_LIST;

  /**
   * The number of districts in the associated candidate list.
   */
  private /*@ spec_public @*/ int my_districtCount; //@ in objectState;
  //@ invariant 0 <= my_districtCount;
  //@ invariant my_districtCount <= KiesKring.MAX_DISTRICTS_PER_KIESKRING;

  /**
   * The number of kieslijsten in the associated candidate list.
   */
  private /*@ spec_public @*/ byte my_kiesLijstCount; //@ in objectState;
  //@ invariant 0 <= my_kiesLijstCount;
  //@ invariant my_kiesLijstCount <= KiesKring.MAX_KIESLIJSTEN_PER_KIESKRING;

  /**
   * The total number of candidates in the associated candidate list.
   */
  private /*@ spec_public @*/ int my_positieCount; //@ in objectState;
  //@ invariant 0 <= my_positieCount;

  /**
   * The number of candidate codes contained in the associated
   * candidate list.
   *
   * @design kiniry 24 March 2004 - No specification has been given
   * for the maximum number of codes, so we assume here that the total
   * can be very large.
   * @design hubbers 26 April 2004 - Typically it will be 1000 codes for
   * each candidate.
   * @design hubbers 28 May 2004 - Apparently it will be 7500 codes for
   * each candidate.
   */
  private /*@ spec_public @*/ int my_codeCount; //@ in objectState;
  //@ invariant 0 <= my_codeCount;


  /**
   * Construct a new candidate list metadata object given the
   * specified initialization values.
   *
   * @param a_request_reference the request reference of the
   * associated candidate list.
   * @param a_response_reference the response reference of the
   * associated candidate list.
   * @param a_creation_time the creation time of the associated
   * candidate list.
   * @param a_kieskring_count the number of kieskringen in the
   * associated candidate list.
   * @param a_district_count the number of districts in the associated
   * candidate list.
   * @param a_kieslijst_count the number of kieslijsten in the
   * associated candidate list.
   * @param a_positie_count the total number of candidates in the
   * associated candidate list.
   * @param a_code_count the number of candidate codes contained in
   * the associated candidate list.
   *
   * @see CandidateList
   *
   * <pre><jml>
   * normal_behavior
   *   requires 0 <= a_kieskring_count;
   *   requires a_kieskring_count <= CandidateList.MAX_KIESKRINGEN_PER_CANDIDATE_LIST;
   *   requires 0 <= a_district_count;
   *   requires a_district_count <= KiesKring.MAX_DISTRICTS_PER_KIESKRING;
   *   requires 0 <= a_kieslijst_count;
   *   requires a_kieslijst_count <= KiesKring.MAX_KIESLIJSTEN_PER_KIESKRING;
   *   requires 0 <= a_positie_count;
   *   requires a_positie_count <= KiesLijst.MAX_CANDIDATES_PER_KIESLIJST * a_kieslijst_count;
   *   requires 0 <= a_code_count;
   *   ensures requestReference().equals(a_request_reference);
   *   ensures responseReference().equals(a_response_reference);
   *   ensures creationTime().equals(a_creation_time);
   *   ensures kiesKringCount() == a_kieskring_count;
   *   ensures districtCount() == a_district_count;
   *   ensures kiesLijstCount() == a_kieslijst_count;
   *   ensures positieCount() == a_positie_count;
   *   ensures codeCount() == a_code_count;
   * </jml></pre>
   */
  /*@ pure @*/ CandidateListMetadata(final /*@ non_null @*/ String a_request_reference,
                                     final /*@ non_null @*/ String a_response_reference,
                                     final /*@ non_null @*/ String a_creation_time,
                                     final byte a_kieskring_count,
                                     final int a_district_count,
                                     final byte a_kieslijst_count,
                                     final int a_positie_count,
                                     final int a_code_count) {
    my_requestReference = a_request_reference;
    my_responseReference = a_response_reference;
    my_creationTime = a_creation_time;
    my_kiesKringCount = a_kieskring_count;
    my_districtCount = a_district_count;
    my_kiesLijstCount = a_kieslijst_count;
    my_positieCount = a_positie_count;
    my_codeCount = a_code_count;
  }

  // Accessors so that we can rely upon invariants and have pure data access.

  /**
   * @return the request reference of the associated candidate list.
   */
  final /*@ pure non_null @*/ String requestReference() {
    return my_requestReference;
  }

  /**
   * @return the response reference of the associated candidate list.
   */
  final /*@ pure non_null @*/ String responseReference() {
    return my_responseReference;
  }

  /**
   * @return the creation time of the associated candidate list.
   */
  final /*@ pure non_null @*/ String creationTime() {
    return my_creationTime;
  }

  /**
   * @return the number of kieskringen in the associated candidate list.
   *
   * <pre><jml>
   * normal_behavior
   *   ensures \result >= 0;
   * </jml></pre>
   */
  final /*@ pure @*/ byte kiesKringCount() {
    return my_kiesKringCount;
  }

  /**
   * @return the number of districts in the associated candidate list.
   *
   * <pre><jml>
   * normal_behavior
   *   ensures \result >= 0;
   * </jml></pre>
   */
  final /*@ pure @*/ int districtCount() {
    return my_districtCount;
  }

  /**
   * @return the number of kieslijst in the associated candidate list.
   *
   * <pre><jml>
   * normal_behavior
   *   ensures \result >= 0;
   * </jml></pre>
   */
  final /*@ pure @*/ byte kiesLijstCount() {
    return my_kiesLijstCount;
  }

  /**
   * @return the total number of candidates in the associated candidate list.
   *
   * <pre><jml>
   * normal_behavior
   *    ensures \result >= 0;
   * </jml></pre>
   */
  final /*@ pure @*/ int positieCount() {
    return my_positieCount;
  }

  /**
   * @return the number of candidate codes in the associated candidate list.
   *
   * <pre><jml>
   * normal_behavior
   *   ensures \result >= 0;
   * </jml></pre>
   */
  final /*@ pure @*/ int codeCount() {
    return my_codeCount;
  }

  /**
   *  Since metadata is non_null we cannot simply throw it away, but just
   *  reset the contents.
   */
  /*@
    @ assignable objectState;
    @ ensures my_requestReference.equals("");
    @ ensures my_responseReference.equals("");
    @ ensures my_creationTime.equals("");
    @ ensures my_kiesKringCount == 0;
    @ ensures my_districtCount == 0;
    @ ensures my_kiesLijstCount == 0;
    @ ensures my_positieCount == 0;
    @ ensures my_codeCount == 0;
    @*/
  public void clear() {
     my_requestReference = "";
     my_responseReference = "";
     my_creationTime = "";
     my_kiesKringCount = 0;
     my_districtCount = 0;
     my_kiesLijstCount = 0;
     my_positieCount = 0;
     my_codeCount = 0;
  }

  // Implementation of Object

  /** {@inheritDoc} */
  public final String toString() {
    return "request reference  : " + requestReference() + "\n" +
      "response reference : " + responseReference() + "\n" +
      "creation time      : " + creationTime() + "\n" +
      "kieskring count    : " + kiesKringCount() + "\n" +
      "district count     : " + districtCount() + "\n" +
      "kieslijstcount     : " + kiesLijstCount() + "\n" +
      "positiecount       : " + positieCount() + "\n" +
      "codecount          : " + codeCount() + "\n";
  }

}
