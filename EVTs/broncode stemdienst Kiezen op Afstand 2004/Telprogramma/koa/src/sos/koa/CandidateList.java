/*
 * JML specification Copyright 2004 SoS Group, University of Nijmegen
 */

package sos.koa;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;
import java.util.SortedMap;
import java.util.TreeMap;

/**
 * The CandidateList stores all of the information embodied in the
 * XML-based candidate list files provided by the KOA application.
 *
 * @author Joe Kiniry (kiniry@cs.kun.nl)
 * @version $Id: CandidateList.java,v 1.37 2004/05/28 20:37:23 hubbers Exp $
 */

class CandidateList
  implements java.io.Serializable
{
  /**
   * The maximum number of kieskringen that can exist in a candidate
   * list.  This maximum is implicit in the fact that a kieskring's
   * number is at most two digits and non-negative.
   */
  static final byte MAX_KIESKRINGEN_PER_CANDIDATE_LIST = 100;

  /**
   * The kieskringen contained in this candidate list.  These
   * kieskringen are arranged in a sorted map so that they can be
   * iterated over by number.
   */
  /* private */ /*@ non_null spec_public @*/ SortedMap my_kieskringen; //@ in objectState;
  //@ maps my_kieskringen.* \into objectState;
  //@ invariant my_kieskringen.size() <= MAX_KIESKRINGEN_PER_CANDIDATE_LIST;
  //@ invariant my_kieskringen.owner == this;

  /**
   * The metadata associated with this candidate list.
   *
   * @design Since this is a required field we may assume it is non-null.
   */
  /* private */ /*@ non_null spec_public @*/ CandidateListMetadata my_metadata; //@ in objectState;
  //@ maps my_metadata.* \into objectState;
  //@ invariant my_metadata.owner == this;

  /**
   * The candidate codes of this candidate list.  Each candidate has
   * one or more unique codes in the candidate list. Typically each
   * candidate will have 1000 codes.
   *
   * @design It is guaranteed that the codes are unique within one
   * candidate list.
   */
  private /*@ non_null spec_public @*/ Map my_candidate_codes; //@ in objectState;
  //@ maps my_candidate_codes.* \into objectState;
  //@ invariant my_candidate_codes.owner == this;

  /**
   * The number of "blanco" candidates contained in this candidate list.
   */
  private /*@ spec_public @*/ byte my_blanco_count; //@ in objectState;
  //@ invariant 0 <= my_blanco_count;


  // Constructors

  /**
   * Construct a new candidate list object given the specified
   * initialization values.
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
   * @see CandidateListMetadata
   *
   * <pre><jml>
   * normal_behavior
   *   requires Byte.parseByte(a_kieskring_count) >= 0;
   *   requires Integer.parseInt(a_district_count) >= 0;
   *   requires Integer.parseInt(a_kieslijst_count) >= 0;
   *   requires Integer.parseInt(a_positie_count) >= 0;
   *   requires Integer.parseInt(a_code_count) >= 0;
   *   modifies objectState;
   *   ensures metadata().requestReference().equals(a_request_reference);
   *   ensures metadata().responseReference().equals(a_response_reference);
   *   ensures metadata().creationTime().equals(a_creation_time);
   *   ensures metadata().kiesKringCount() == Byte.parseByte(a_kieskring_count);
   *   ensures metadata().districtCount() == Integer.parseInt(a_district_count);
   *   ensures metadata().positieCount() == Integer.parseInt(a_positie_count);
   *   ensures metadata().codeCount() == Integer.parseInt(a_code_count);
   * </jml></pre>
   */
  /*@ pure @*/ CandidateList(final /*@ non_null @*/ String a_request_reference,
                             final /*@ non_null @*/ String a_response_reference,
                             final /*@ non_null @*/ String a_creation_time,
                             final /*@ non_null @*/ String a_kieskring_count,
                             final /*@ non_null @*/ String a_district_count,
                             final /*@ non_null @*/ String a_kieslijst_count,
                             final /*@ non_null @*/ String a_positie_count,
                             final /*@ non_null @*/ String a_code_count) {
    my_metadata = new CandidateListMetadata(a_request_reference,
                                            a_response_reference,
                                            a_creation_time,
                                            Byte.parseByte(a_kieskring_count),
                                            Integer.parseInt(a_district_count),
                                            Byte.parseByte(a_kieslijst_count),
                                            Integer.parseInt(a_positie_count),
                                            Integer.parseInt(a_code_count));
    my_kieskringen = new TreeMap();
    my_candidate_codes = new HashMap(my_metadata.codeCount());
    //@ set my_metadata.owner = this;
    //@ set my_kieskringen.owner = this;
    //@ set my_candidate_codes.owner = this;
  }


  // Setter/adder methods

  /**
   * Add the specified kieskring to this candidate list.
   *
   * @param a_kieskring_number the number of the kieskring to add.
   * @param a_name the name of the kieskring to add.
   * @return the newly added kieskring.
   *
   * @see KiesKring#make(byte, java.lang.String)
   *
   * <pre><jml>
   * normal_behavior
   *   requires (* all parameters must be of the proper length *);
   *   requires 0 <= a_kieskring_number;
   *   requires a_kieskring_number <= MAX_KIESKRINGEN_PER_CANDIDATE_LIST;
   *   requires a_name.length() <= KiesKring.KIESKRING_NAME_MAX_LENGTH;
   *   modifies \everything;
   *   ensures (* all fields are properly initialized *);
   *   ensures \result.number() == a_kieskring_number;
   *   ensures \result.name().equals(a_name);
   * </jml></pre>
   */
  /*@ non_null @*/ final KiesKring addKiesKring(final byte a_kieskring_number,
                                                final /*@ non_null @*/ String a_name) {
    final KiesKring kiesKring = KiesKring.make(a_kieskring_number, a_name);
    my_kieskringen.put(new Byte(kiesKring.number()), kiesKring);
    //@ set kiesKring.owner = this;
    return kiesKring;
  }

  /**
   * Add the specified district, contained in a specific kieskring, to
   * this candidate list.
   *
   * @param a_kieskring the kieskring in which the district being
   * added resides.
   * @param a_district_number the number of the district to add.
   * @param a_name the name of the district to add.
   * @return the newly added district.
   *
   * @see sos.koa.District#District(sos.koa.KiesKring, int, java.lang.String)
   *
   * @design kiniry 5 April 2004 - Why did this method used to store
   * the constructed district somewhere?  Is this no longer necessary?
   * This method was not pure before, but seems to be now.
   *
   * <pre><jml>
   * normal_behavior
   *   requires 0 <= a_district_number;
   *   requires a_district_number <= KiesKring.MAX_DISTRICTS_PER_KIESKRING;
   *   requires a_name.length() <= District.DISTRICT_NAME_MAX_LENGTH;
   *   modifies a_kieskring.objectState;
   *   ensures a_kieskring.hasDistrict(\result);
   *   ensures \result.number() == a_district_number;
   *   ensures \result.name().equals(a_name);
   * </jml></pre>
   */
  final /*@ non_null @*/ District
    addDistrict(final /*@ non_null @*/ KiesKring a_kieskring,
                final int a_district_number,
                final /*@ non_null @*/ String a_name) {
    final District d = new District(a_district_number, a_name);
    a_kieskring.addDistrict(d);
    return d;
  }

  /**
   * Add the specified kieslijst, contained in a specific kieskring,
   * to this candidate list.
   *
   * @param a_kieskring the kieskring in which the district being
   * added resides.
   * @param a_kieslijst_number the number of the kieslijst to add.
   * @param a_groepering_name the name of the groupering to add.
   * @return the newly added kieslijst.
   *
   * @see sos.koa.KiesLijst#KiesLijst(byte, byte, java.lang.String)
   *
   * <pre><jml>
   * normal_behavior
   *   requires 0 <= a_kieslijst_number;
   *   requires a_kieslijst_number <= KiesKring.MAX_KIESLIJSTEN_PER_KIESKRING;
   *   requires a_groepering_name.length() <= KiesLijst.GROEPERING_NAME_MAX_LENGTH;
   *   requires a_kieskring.hasKiesLijst(KiesLijst.make(a_kieskring.number(), a_kieslijst_number, a_groepering_name));
   *   modifies \nothing;
   *   ensures \result.equals(KiesLijst.make(a_kieskring.number(), a_kieslijst_number, a_groepering_name));
   * also
   * normal_behavior
   *   requires !a_kieskring.hasKiesLijst(KiesLijst.make(a_kieskring.number(), a_kieslijst_number, a_groepering_name));
   *   modifies a_kieskring.my_kiesLijsten[a_kieslijst_number];
   *   ensures a_kieskring.hasKiesLijst(KiesLijst.make(a_kieskring.number(), a_kieslijst_number, a_groepering_name));
   *   ensures a_kieskring.kieslijstCount() == \old(a_kieskring.kieslijstCount() + 1);
   *   ensures \result.equals(KiesLijst.make(a_kieskring.number(), a_kieslijst_number, a_groepering_name));
   * </jml></pre>
   */
  /*@ non_null @*/ final KiesLijst
    addKiesLijst(final /*@ non_null @*/ KiesKring a_kieskring,
                 final byte a_kieslijst_number,
                 final /*@ non_null @*/ String a_groepering_name) {
    final KiesLijst k = KiesLijst.make(a_kieskring.number(),
                                       a_kieslijst_number,
                                       a_groepering_name);
    a_kieskring.addKiesLijst(k);
    //@ set k.owner = this;
    return k;
  }

  /**
   * Add the specified candidate to this candidate list.
   *
   * @param a_kieskring the kieskring to which the candidate belongs.
   * @param a_kieslijst the kieslijst to which the candidate belongs.
   * @param a_position_number the position number of the candidate.
   * @param a_lastname the lastname of the new candidate.
   * @param a_firstname the firstname of the new candidate.
   * @param some_initials the initial of the new candidate.
   * @param a_gender the gender of the new candidate.
   * @param a_city_of_residence the city of residence of the new
   * candidate.
   * @return the newly added candidate.
   *
   * <pre><jml>
   * normal_behavior
   *   requires (* all parameters must be of the proper length *);
   *   requires a_lastname.length() <= Candidate.LASTNAME_MAX_LENGTH;
   *   requires a_firstname.length() <= Candidate.FIRSTNAME_MAX_LENGTH;
   *   requires some_initials.length() <= Candidate.INITIALS_MAX_LENGTH;
   *   requires a_gender.length() == 1;
   *   requires a_gender.charAt(0) == Candidate.MALE || a_gender.charAt(0) == Candidate.FEMALE || a_gender.charAt(0) == Candidate.UNKNOWN;
   *   requires 0 <= Byte.parseByte(a_position_number);
   *   requires Byte.parseByte(a_position_number) <= KiesLijst.MAX_CANDIDATES_PER_KIESLIJST;
   *   modifies \nothing;
   *   ensures (* all fields are properly initialized *);
   *   ensures \result.lastname().equals(a_lastname);
   *   ensures \result.firstname().equals(a_firstname);
   *   ensures \result.initials().equals(some_initials);
   *   ensures \result.gender() == a_gender.charAt(0);
   *   ensures \result.position_number() == Byte.parseByte(a_position_number);
   *   ensures \result.cityOfResidence().equals(a_city_of_residence);
   *   ensures \result.kiesKring().equals(a_kieskring);
   *   ensures \result.kiesLijst().equals(a_kieslijst);
   * also
   * normal_behavior
   *   requires (* Is the position of 1 REQUIRED? -JRK *);
   *   requires a_kieslijst.number() == KiesLijst.BLANCO;
   *   requires Byte.parseByte(a_position_number) == 1;
   *   modifies my_blanco_count;
   *   ensures my_blanco_count == \old(my_blanco_count + 1);
   * </jml></pre>
   */
  final /*@ non_null @*/ Candidate
    addCandidate(final /*@ non_null @*/ KiesKring a_kieskring,
                 final /*@ non_null @*/ KiesLijst a_kieslijst,
                 final /*@ non_null @*/ String a_position_number,
                 final /*@ non_null @*/ String a_lastname,
                 final /*@ non_null @*/ String some_initials,
                 final /*@ non_null @*/ String a_firstname,
                 final /*@ non_null @*/ String a_gender,
                 final /*@ non_null @*/ String a_city_of_residence) {
    // @design It is confirmed by the ministry that the position number
    // will always be 1.
    if ((a_kieslijst.number() == KiesLijst.BLANCO) &&
        (Byte.parseByte(a_position_number) == 1)) {
      my_blanco_count++;
    }
    final Candidate c = new Candidate(a_lastname, a_firstname, some_initials,
                                      a_gender.charAt(0),
                                      Byte.parseByte(a_position_number),
                                      a_city_of_residence,
                                      a_kieskring, a_kieslijst);
    //@ set c.owner = this;
    return c;
  }

  /**
   * Adds the specified candidiate code, bound to the specified
   * candidate, to this candidate list.
   *
   * @param a_candidate the candidate to which we bind the candidate code.
   * @param a_candidate_code the candidate code to bind to the candidate.
   * @return a flag indicating if the specified candidate code previously
   * had a candidate associated with it.
   *
   * <pre><jml>
   * normal_behavior
   *   requires 0 <= Integer.parseInt(a_candidate_code);
   *   modifies my_candidate_codes.objectState;
   *   ensures \result <==> (\old(getCandidate(a_candidate_code) == null));
   * </jml></pre>
   */
  final boolean addCandidateCode(final /*@ non_null @*/ Candidate a_candidate,
                                 final /*@ non_null @*/ String a_candidate_code) {
    return my_candidate_codes.put(new Integer(Integer.parseInt(a_candidate_code)), a_candidate) == null;
  }


  // Getters

  // The two getCandidate() methods, and the two validCandidate()
  // methods, are equivalent.

  //@ invariant (\forall int i; getCandidate(i) == getCandidate(Integer.toString(i)));
  //@ invariant (\forall int i; validCandidate(i) == validCandidate(Integer.toString(i)));

  /**
   * @param a_candidate_code the candidate code we are interested in.
   * @return the candidate in this candidate list associated with the
   * specified candidate code.
   *
   * <pre><jml>
   * normal_behavior
   *   requires 0 <= Integer.parseInt(a_candidate_code);
   *   requires validCandidate(a_candidate_code);
   *   ensures \result == my_candidate_codes.get(new Integer(Integer.parseInt(a_candidate_code)));
   * </jml></pre>
   */
  final /*@ pure non_null @*/ Candidate getCandidate(final /*@ non_null @*/ String a_candidate_code) {
    return (Candidate)(my_candidate_codes.get(new Integer(Integer.parseInt(a_candidate_code))));
  }

  /**
   * @param a_candidate_code the candidate code we are interested in.
   * @return a flag indicating if the specified candidate code is a
   * valid candidate code for this candidate list.  That is to say,
   * the specified code is associated with a candidate in this
   * candidate list.
   *
   * <pre><jml>
   * normal_behavior
   *   requires 0 <= Integer.parseInt(a_candidate_code);
   *   ensures \result == my_candidate_codes.containsKey(new Integer(Integer.parseInt(a_candidate_code)));
   * </jml></pre>
   */
  final /*@ pure @*/ boolean validCandidate(final /*@ non_null @*/ String a_candidate_code) {
    return my_candidate_codes.containsKey(new Integer(Integer.parseInt(a_candidate_code)));
  }

  /**
   * @param a_candidate_code the candidate code we are interested in.
   * @return the candidate in this candidate list associated with the
   * specified candidate code.
   *
   * <pre><jml>
   * normal_behavior
   *   requires 0 <= a_candidate_code;
   *   requires validCandidate(a_candidate_code);
   *   ensures \result == my_candidate_codes.get(new Integer(a_candidate_code));
   * </jml></pre>
   */
  final /*@ pure non_null @*/ Candidate getCandidate(final int a_candidate_code) {
    return (Candidate)(my_candidate_codes.get(new Integer(a_candidate_code)));
  }

  /**
   * @param a_candidate_code the candidate code we are interested in.
   * @return a flag indicating if the specified candidate code is a
   * valid candidate code for this candidate list.  That is to say,
   * the specified code is associated with a candidate in this
   * candidate list.
   *
   * <pre><jml>
   * normal_behavior
   *   requires 0 <= a_candidate_code;
   *   ensures \result == my_candidate_codes.containsKey(new Integer(a_candidate_code));
   * </jml></pre>
   */
  final /*@ pure @*/ boolean validCandidate(final int a_candidate_code) {
    return my_candidate_codes.containsKey(new Integer(a_candidate_code));
  }

  /**
   * @return the metadata associated with this candidate list.
   *
   * <pre><jml>
   * normal_behavior
   *   ensures \result == my_metadata;
   * </jml></pre>
   */
  final /*@ pure non_null @*/ CandidateListMetadata metadata() {
    return my_metadata;
  }

  /**
   * @param a_kieslijst the kieslijst (party) that we are interested in.
   * @return the number of candidates in the specified kieslijst (party).
   *
   * <pre><jml>
   * normal_behavior
   *   ensures 0 <= \result;
   * </jml></pre>
   */
  final /*@ pure @*/ byte candidatesPerParty(final /*@ non_null @*/ KiesLijst a_kieslijst) {
    return a_kieslijst.candidateCount();
  }

  /**
   * @return the total number of kieslijsten (parties) contained in
   * this candidate list.
   *
   * <pre><jml>
   * normal_behavior
   *   ensures 0 <= \result && \result <= KiesKring.MAX_KIESLIJSTEN_PER_KIESKRING;
   * also
   * normal_behavior
   *   requires (* if there are more than MAX_KIESLIJSTEN_PER_KIESKRING kieslijsten in any kieskring *);
   *   ensures (* false *);
   * </jml></pre>
   */
  final /*@ pure @*/ byte totalPartyCount() {
    // for each kieskring, add its kieslijst count to the total.
    int result = 0;
    final Set orderedCodes = my_kieskringen.keySet();
    if (orderedCodes == null) {
      return 0;
    }
    assert (orderedCodes != null);
    final Iterator i = orderedCodes.iterator();
    assert (i != null);
    while (i.hasNext()) {
      final Byte b = (Byte)(i.next());
      final KiesKring kiesKring = (KiesKring)(my_kieskringen.get(b));
      result = result + kiesKring.kieslijstCount();
    }
    assert (result <= KiesKring.MAX_KIESLIJSTEN_PER_KIESKRING);
    return (byte)result;
  }

  /**
   * @return the total number of "blanco" kieslijsten contained in
   * this candidate list.
   *
   * @see KiesLijst#BLANCO
   *
   * <pre><jml>
   * normal_behavior
   *   ensures 0 <= \result;
   *   ensures \result == my_blanco_count;
   * </jml></pre>
   */
  final /*@ pure @*/ byte blancoCount() {
    return my_blanco_count;
  }

  /**
   * Clears all data in this <code>CandidateList</code> instance. In
   * particular, all kieskring references are cleared.
   *
   * <pre><jml>
   * normal_behavior
   *   modifies objectState;
   *
   *   ensures my_kieskringen.isEmpty();
   *   ensures my_candidate_codes.isEmpty();
   *   ensures my_blanco_count == 0;
   *
   *   ensures_redundantly (\forall int i; getCandidate(i) == null);
   *   ensures_redundantly (\forall int i; !validCandidate(i));
   *   ensures_redundantly (\forall KiesLijst kl; candidatesPerParty(kl) == 0);
   *   ensures_redundantly (* totalPartyCount() == 0; *);
   *   ensures_redundantly blancoCount() == 0;
   * </jml></pre>
   */
  final void clear() {
    if (my_kieskringen != null) {
      final Set ordered_kieskringen = my_kieskringen.keySet();
      assert (ordered_kieskringen != null);
      final Iterator i = ordered_kieskringen.iterator();
      assert (i != null);
      while (i.hasNext()) {
        final Byte b = (Byte)(i.next());
        final KiesKring kiesKring = (KiesKring)(my_kieskringen.get(b));
        kiesKring.clear();
      }
    }
    my_kieskringen.clear();
    my_candidate_codes.clear();
    // Since my_metadata is non_null we simply reset the contents of it.
    my_metadata.clear();
    my_blanco_count = 0;
  }

  /*@ pure @*/ public SortedMap getKiesKringen() {
    return my_kieskringen;
  }
}
