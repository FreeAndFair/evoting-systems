/*
 * JML specification Copyright 2004 SoS Group, University of Nijmegen
 */

package sos.koa;

/**
 * A district is a region of the country within a kieskring.  Each kieskring has
 * one or more districts.
 *
 * @author Joe Kiniry (kiniry@cs.kun.nl)
 * @version $Id: District.java,v 1.21 2004/05/16 20:37:39 kiniry Exp $
 */

class District
  implements Comparable, java.io.Serializable
{
  /**
   * The maximum length, in digits, of a district's number.
   *
   * @design As specified by the LogicaCMG specification, the district
   * number is encoded as char[5], thus its maximum length is 5.
   */
  static final byte DISTRICT_NUMBER_MAX_LENGTH = 5;

  /**
   * The maximum length, in characters, of a district's name.
   *
   * @design Not specified by the LogicaCMG documentation, but given by
   * the ministry directly.
   */
  static final byte DISTRICT_NAME_MAX_LENGTH = 80;

  /**
   * The number of this district.
   */
  private /*@ spec_public @*/ int my_number; //@ in objectState;
  //@ invariant 0 <= my_number && my_number <= KiesKring.MAX_DISTRICTS_PER_KIESKRING;

  /**
   * The name of this district.
   *
   */
  private /*@ non_null spec_public @*/ String my_name; //@ in objectState;
  //@ invariant my_name.length() <= DISTRICT_NAME_MAX_LENGTH;

  /**
   * Each district is in exactly one {@link KiesKring}.
   */
  private /*@ spec_public @*/ KiesKring my_kiesKring; //@ in objectState;
  //@ invariant (my_kiesKring != null) ==> this.owner == my_kiesKring;


  // Constructors

  /**
   * Construct a new district object given the specified
   * initialization values.
   *
   * @param a_district_number the number of the new district.
   * @param a_district_name the name of the new district.
   *
   * <pre><jml>
   * private normal_behavior
   *   requires 0 <= a_district_number;
   *   requires a_district_number <= KiesKring.MAX_DISTRICTS_PER_KIESKRING;
   *   requires a_district_name.length() <= DISTRICT_NAME_MAX_LENGTH;
   *   modifies \everything;
   *   ensures number() == a_district_number;
   *   ensures name().equals(a_district_name);
   * </jml></pre>
   */
  District (final int a_district_number,
            final /*@ non_null @*/ String a_district_name) {
    my_number = a_district_number;
    my_name = a_district_name;
    // @verification kiniry 16 May 2004 - String semantics for
    // ESC/Java2 are incomplete.  The postcondition
    // name().equals(a_district_name) is valid due to the assignment
    // my_name = a_district_name, the fact that name() returns
    // my_name, and s.equals(s) for all s <: String.
  } //@ nowarn Post;

  /**
   * Clears the information of this district.
   *
   * <pre><jml>
   * normal_behavior
   *   modifies objectState;
   *   ensures number() == 0;
   *   ensures name().equals("");
   *   ensures kiesKring() == null;
   * </jml></pre>
   */
  final void clear() {
    my_number = 0;
    my_name = "";
    my_kiesKring = null;
    // @verification kiniry 16 May 2004 - String semantics for
    // ESC/Java2 are incomplete.  The postcondition
    // name().equals("") is valid due to the assignment
    // my_name = "", and "".equals("").
  } //@ nowarn Post;


  // Accessors so that we can rely upon invariants and have pure data access.

  /**
   * @return the number of this district.
   *
   * <pre><jml>
   * normal_behavior
   *   ensures 0 <= \result && \result <= KiesKring.MAX_DISTRICTS_PER_KIESKRING;
   *   ensures \result == my_number;
   * </jml></pre>
   */
  final /*@ pure @*/ int number() {
    return my_number;
  }

  /**
   * @return the name of this district.
   *
   * <pre><jml>
   * normal_behavior
   *   ensures \result.length() <= DISTRICT_NAME_MAX_LENGTH;
   *   ensures \result == my_name;
   * </jml></pre>
   */
  final /*@ pure non_null @*/ String name() {
    return my_name;
  }

  /**
   * @return the kieskring of this district.
   *
   * <pre><jml>
   * normal_behavior
   *   ensures \result == my_kiesKring;
   * </jml></pre>
   */
  final /*@ pure @*/ KiesKring kiesKring() {
    return my_kiesKring;
  }


  // Implementation of Object

  /** {@inheritDoc} */
  public final boolean equals(final Object an_object) {
    if (an_object == null) {
      return false;
    }

    if (!(an_object instanceof District)) {
      return false;
    }
    final District d = (District) an_object;

    return d.my_number == this.my_number &&
      d.my_name.equals(this.my_name);
  }

  /** {@inheritDoc} */
  public final int hashCode() {
    return my_name.hashCode(); //@ nowarn Modifies;
  }

  /** {@inheritDoc} */
  public final String toString() {
    return my_number + "." + (my_number < 10 ? "  " : " ") + my_name;
    // @verification kiniry 16 May 2004 - String concatenation semantics for 
    // ESC/Java2 are incomplete.  The postcondition "\result != null" of 
    // this method is valid because my_name is non-null.
  } //@ nowarn Post;


  // Implementation of Comparable

  /** {@inheritDoc} */
  public final int compareTo(final Object an_object) {
    if (!(an_object instanceof District)) {
      throw new ClassCastException();
    }

    final District d = (District) an_object;
    return this.my_number - d.my_number;
  } //@ nowarn Exception, Post;
}
