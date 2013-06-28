/*
 * JML specification Copyright 2004 SoS Group, University of Nijmegen
 */

package sos.koa;

/**
 * A candidate in an election.
 *
 * @author Joe Kiniry (kiniry@cs.kun.nl)
 * @version $Id: Candidate.java,v 1.31 2004/05/28 20:37:23 hubbers Exp $
 */

public class Candidate
  implements Comparable, java.io.Serializable
{
  /**
   * The maximum length, in character, of the lastname (surname) of a
   * candidate.
   *
   * @design As specified by the LogicaCMG specification, the lastname
   * in the stemmen file is encoded as char[80], thus its maximum
   * length is 80.
   *
   * @design According to the ministry we may assume that the input file 
   * only contains fields with proper length.
   */
  static final byte LASTNAME_MAX_LENGTH = 80;

  /**
   * The maximum length, in characters, of the firstname of a
   * candidate.
   *
   * @design There is no specification provided
   * by the LogicaCMG document for this field whatsoever.
   * This value was guessed and later on approved by the ministry.
   */
  static final byte FIRSTNAME_MAX_LENGTH = 80;

  /**
   * The maximum length, in characters, of the initials of a
   * candidate.
   *
   * @design As specified by the LogicaCMG specification, the
   * voorletters in the stemmen file is encoded as char[20], thus its
   * maximum length is 20.
   * @design According to the ministry we may assume that the input file 
   * only contains fields with proper length.
   */
  static final byte INITIALS_MAX_LENGTH = 20;

  /**
   * The possible values of the gender of a candidate.
   *
   * @design The UNKNOWN is added because the sample files provided by
   * the ministry contained this value. This is approved by the ministry.
   */
  static final char MALE = 'M', FEMALE = 'V', UNKNOWN = ' ';

  /**
   * The maximum length, in digits represented by characters, of the
   * position number of a candidate.
   *
   * @design As specified by the LogicaCMG specification, the
   * positienummer in the stemmen file is encoded as char[2], thus
   * its maximum length is 2.
   * @design According to the ministry we may assume that the input file 
   * only contains fields with proper length.
   */
  static final byte POSITION_NUMBER_MAX_LENGTH = 2;

  /**
   * The maximum length, in digits represented by characters, of the
   * city of residence of a candidate.
   *
   * @design Not specified by the LogicaCMG documentation, but given by
   * the ministry directly.
   * @design According to the ministry we may assume that the input file 
   * only contains fields with proper length.
   */
  static final byte CITY_OF_RESIDENCE_MAX_LENGTH = 80;

  /**
   * The lastname (achternaam) of a candidate.
   */
  private /*@ non_null spec_public @*/ String my_lastname; //@ in objectState;
  //@ invariant my_lastname.length() <= LASTNAME_MAX_LENGTH;
  //@ invariant my_lastname.owner == this;

  /**
   * The firstname (roepnaam) of a candidate.
   *
   */
  private /*@ non_null spec_public @*/ String my_firstname; //@ in objectState;
  //@ invariant my_firstname.length() <= FIRSTNAME_MAX_LENGTH;
  //@ invariant my_firstname.owner == this;

  /**
   * The initials (voorletters) of a candidate.
   */
  private /*@ non_null spec_public @*/ String my_initials; //@ in objectState;
  //@ invariant my_initials.length() <= INITIALS_MAX_LENGTH;
  //@ invariant my_initials.owner == this;

  /**
   * The gender (geslacht) of a candidate.
   */
  private /*@ spec_public @*/ char my_gender; //@ in objectState;
  //@ invariant my_gender == MALE || my_gender == FEMALE || my_gender == UNKNOWN;

  /**
   * The position number (positienummer) of a candidate.
   */
  private /*@ spec_public @*/ byte my_position_number; //@ in objectState;
  //@ invariant 0 <= my_position_number;
  //@ invariant my_position_number <= KiesLijst.MAX_CANDIDATES_PER_KIESLIJST;

  /**
   * The city of residence (woonplaats) of a candidate.
   *
   * @design Because it is a required field we declare it as non-null.
   */
  private /*@ non_null spec_public @*/ String my_city_of_residence; //@ in objectState;
  //@ invariant my_city_of_residence.length() <= CITY_OF_RESIDENCE_MAX_LENGTH;
  //@ invariant my_city_of_residence.owner == this;

  /**
   * The kieskring of a candidate.
   */
  private /*@ non_null spec_public @*/ KiesKring my_kiesKring; //@ in objectState;

  /**
   * The kieslijst of a candidate.
   */
  private /*@ non_null spec_public @*/ KiesLijst my_kiesLijst; //@ in objectState;

  /**
   * The number of votes cast for this candidate.
   */
  private /*@ spec_public @*/ int my_vote_count; //@ in objectState;
  //@ invariant my_vote_count >= 0;
  // Because AuditLog.setCountNrOfVotes() is not called yet we can
  // only compare with AuditLog.getDecryptNrOfVotes().
  //@ invariant my_vote_count <= AuditLog.getDecryptNrOfVotes();


  /**
   * Construct a new candidate object given the specified
   * initialization values.
   *
   * @param a_lastname the lastname of the new candidate.
   * @param a_firstname the firstname of the new candidate.
   * @param some_initials the initial of the new candidate.
   * @param a_gender the gender of the new candidate.
   * @param a_position_number the position number of the new candidate.
   * @param a_city_of_residence the city of residence of the new
   * candidate.
   * @param a_kieskring the kieskring of the new candidate.
   * @param a_kieslijst the kieslijst of the new candidate.
   *
   * <pre><jml>
   * normal_behavior
   *   requires (* all parameters must be of the proper length *);
   *   requires a_lastname.length() <= LASTNAME_MAX_LENGTH;
   *   requires a_firstname.length() <= FIRSTNAME_MAX_LENGTH;
   *   requires some_initials.length() <= INITIALS_MAX_LENGTH;
   *   requires a_gender == MALE || a_gender == FEMALE || a_gender == UNKNOWN;
   *   requires 0 <= a_position_number;
   *   requires a_position_number <= KiesLijst.MAX_CANDIDATES_PER_KIESLIJST;
   *   requires a_city_of_residence.length() <= CITY_OF_RESIDENCE_MAX_LENGTH;
   *   requires a_kieslijst.candidateCount() < KiesLijst.MAX_CANDIDATES_PER_KIESLIJST;
   *   modifies \everything;
   *   ensures (* all fields are properly initialized *);
   *   ensures lastname().equals(a_lastname);
   *   ensures firstname().equals(a_firstname);
   *   ensures initials().equals(some_initials);
   *   ensures gender() == a_gender;
   *   ensures position_number() == a_position_number;
   *   ensures cityOfResidence().equals(a_city_of_residence);
   *   ensures kiesKring().equals(a_kieskring);
   *   ensures kiesLijst().equals(a_kieslijst);
   *   ensures kiesLijst().candidateCount() == \old(a_kieslijst.candidateCount() + 1);
   * </jml></pre>
   */
  Candidate(final /*@ non_null @*/ String a_lastname,
            final /*@ non_null @*/ String a_firstname,
            final /*@ non_null @*/ String some_initials,
            final char a_gender,
            final byte a_position_number,
            final /*@ non_null @*/ String a_city_of_residence,
            final /*@ non_null @*/ KiesKring a_kieskring,
            final /*@ non_null @*/ KiesLijst a_kieslijst) {
    my_lastname = a_lastname;
    my_firstname = a_firstname;
    my_initials = some_initials;
    my_gender = a_gender;
    my_position_number = a_position_number;
    my_city_of_residence = a_city_of_residence;
    my_kiesKring = a_kieskring;
    my_kiesLijst = a_kieslijst;
    //@ set my_lastname.owner = this;
    //@ set my_firstname.owner = this;
    //@ set my_initials.owner = this;
    //@ set my_city_of_residence.owner = this;
    my_kiesLijst.addCandidate(this);
  }


  // Accessors so that we can rely upon invariants and have pure data access.

  /**
   * @return the lastname of this candidate.
   *
   * <pre><jml>
   * normal_behavior
   *   ensures \result.length() <= LASTNAME_MAX_LENGTH;
   * </jml></pre>
   */
  final /*@ pure non_null @*/ String lastname() {
    return my_lastname;
  }

  /**
   * @return the firstname of this candidate.
   *
   * <pre><jml>
   * normal_behavior
   *   ensures \result.length() <= FIRSTNAME_MAX_LENGTH;
   * </jml></pre>
   */
  final /*@ pure non_null @*/ String firstname() {
    return my_firstname;
  }

  /**
   * @return the initials of this candidate.
   *
   * <pre><jml>
   * normal_behavior
   *   ensures \result.length() <= INITIALS_MAX_LENGTH;
   * </jml></pre>
   */
  final /*@ pure non_null @*/ String initials() {
    return my_initials;
  }

  /**
   * @return the gender of this candidate.
   *
   * <pre><jml>
   * normal_behavior
   *   ensures \result == MALE || \result == FEMALE || \result == UNKNOWN;
   * </jml></pre>
   */
  final /*@ pure @*/ char gender() {
    return my_gender;
  }

  /**
   * @return the position number of this candidate.
   *
   * <pre><jml>
   * normal_behavior
   *   ensures 0 <= \result && \result <= KiesLijst.MAX_CANDIDATES_PER_KIESLIJST;
   * </jml></pre>
   */
  final /*@ pure @*/ byte position_number() {
    return my_position_number;
  }

  /**
   * @return the city of residence of this candidate.
   */
  final /*@ pure non_null @*/ String cityOfResidence() {
    return my_city_of_residence;
  }

  /**
   * @return the kieskring of this candidate.
   *
   * <pre><jml>
   * normal_behavior
   *   ensures \result == my_kiesKring;
   * </jml></pre>
   */
  final /*@ pure non_null @*/ KiesKring kiesKring() {
      return my_kiesKring;
  }

  /**
   * @return the kieslijst of this candidate.
   *
   * <pre><jml>
   * normal_behavior
   *   ensures \result == my_kiesLijst;
   * </jml></pre>
   */
  final /*@ pure non_null @*/ KiesLijst kiesLijst() {
    return my_kiesLijst;
  }


  // Vote count

  /**
   * @return the vote count of this candidate.
   *
   * <pre><jml>
   * normal_behavior
   *   requires my_vote_count < AuditLog.getDecryptNrOfVotes();
   *   modifies my_vote_count;
   *   ensures my_vote_count == \old(my_vote_count + 1);
   * </jml></pre>
   */
  final int incrementVoteCount() {
    my_vote_count = my_vote_count + 1;
    return my_vote_count;
  }

  /**
   * @return the vote count of this candidate.
   *
   * <pre><jml>
   * normal_behavior
   *   ensures \result == my_vote_count;
   * </jml></pre>
   */
  final /*@ pure @*/ int voteCount() {
    return my_vote_count;
  }

  /**
   * Reset the vote count for this candidate.
   *
   * <pre><jml>
   * normal_behavior
   *   modifies my_vote_count;
   *   ensures my_vote_count == 0;
   * </jml></pre>
   */
  final void resetVoteCount() {
    my_vote_count = 0;
  }


  // Implementation of Object


  /** {@inheritDoc} */
  public final boolean equals(final Object an_object) {
    if (an_object == null) {
      return false;
    }

    if (!(an_object instanceof Candidate)) {
      return false;
    }
    final Candidate ci = (Candidate)an_object;

    return ci.lastname().equals(lastname()) &&
      ci.firstname().equals(firstname()) &&
      ci.initials().equals(initials()) &&
      ci.position_number() == position_number() &&
      ci.kiesKring().equals(kiesKring()) &&
      ci.kiesLijst().equals(kiesLijst());
  }

  /** {@inheritDoc} */
  public final int hashCode() {
    return (lastname() + firstname() + initials()).hashCode(); //@ nowarn Modifies;
  }

  /** {@inheritDoc} */
  public final String toString() {
    return position_number() + "." + (position_number() < 10 ? "  " : " ") +
      initials() + " " + lastname() + " (" + firstname() + ")\n" +
      "kieskring :  " + kiesKring() +
      "kieslijst :  " + kiesLijst();
  } //@ nowarn Post;


  // Implementation of Comparable

  /** {@inheritDoc} */
  public final int compareTo(final Object an_object) {
    if (!(an_object instanceof Candidate)) {
      throw new ClassCastException();
    }

    final Candidate ci = (Candidate) an_object;
    return position_number() - ci.position_number();
  } //@ nowarn Exception, Post;
}
