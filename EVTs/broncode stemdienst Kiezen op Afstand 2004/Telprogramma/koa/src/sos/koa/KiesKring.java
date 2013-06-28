/*
 * JML specification Copyright 2004 SoS Group, University of Nijmegen
 */

package sos.koa;

/**
 * A kieskring in an election.
 *
 * @author Joe Kiniry (kiniry@cs.kun.nl)
 * @version $Id: KiesKring.java,v 1.31 2004/05/16 20:37:39 kiniry Exp $
 */

final class KiesKring
  implements Comparable, java.io.Serializable
{
  /**
   * The maximum length, in digits represented by characters, of the
   * number of a kieskring.
   *
   * @design As specified by the LogicaCMG specification, the
   * kieskringnummer in the stemmen file is encoded as char[2], thus
   * its maximum length is 2.
   * @design According to the ministry we may assume that the input file 
   * only contains fields with proper length.
   */
  static final byte KIESKRING_NUMBER_MAX_LENGTH = 2;

  /**
   * The maximum length, in characters, of the name of a kieskring.
   *
   * @design Not specified by the LogicaCMG documentation, but given by
   * the ministry directly.
   */
  static final byte KIESKRING_NAME_MAX_LENGTH = 80;

  /**
   * The maximum number of districts that can exist in a single
   * kieskring.
   *
   * @design As specified by the LogicaCMG specification, the
   * districtnummer in the stemmen file is encoded as char[5], thus
   * its maximum length is 5.
   * @design According to the ministry we may assume that the input file 
   * only contains fields with proper length. There is no maximum defined
   * by law.
   */
  static final int MAX_DISTRICTS_PER_KIESKRING = 100000;

  /**
   * The maximum number of kieslijsten that can exist in a single
   * kieskring.
   *
   * @design As specified by the LogicaCMG specification, the
   * kieslijstnummer in the stemmen file is encoded as char[2], thus
   * its maximum length is 2.
   * @design According to the ministry we may assume that the input file 
   * only contains fields with proper length. There is no maximum defined
   * by law.
   */
  static final byte MAX_KIESLIJSTEN_PER_KIESKRING = 100;

  /**
   * A cache of all kieskringen that have been constructed thus far.
   * This cache is used by the factory method {@link #make(byte,
   * java.lang.String)}.
   */
  private static final /*@ non_null spec_public @*/ KiesKring[] MY_CACHED_KIESKRINGEN =
    new KiesKring [CandidateList.MAX_KIESKRINGEN_PER_CANDIDATE_LIST + 1];
  //@ invariant (\forall int i; 0 <= i && i < MY_CACHED_KIESKRINGEN.length; MY_CACHED_KIESKRINGEN[i].owner == MY_CACHED_KIESKRINGEN);

  /**
   * A list of all kieslijst in this kieskring, indexed on kieslijst
   * number.
   *
   * @design Note that, since kieslijst numbers
   * are not guaranteed sequential, we cannot state anything about the
   * contents of this array.
   */
  final /*@ non_null spec_public @*/ KiesLijst[] my_kiesLijsten =
    new KiesLijst [MAX_KIESLIJSTEN_PER_KIESKRING + 1]; //@ in objectState;
  //@ maps my_kiesLijsten[*] \into objectState;
  //@ invariant my_kiesLijsten.length == MAX_KIESLIJSTEN_PER_KIESKRING + 1;
  //@ invariant my_kiesLijsten.owner == this;
  //@ invariant (\forall int i; 0 <= i && i < my_kiesLijsten.length; my_kiesLijsten[i].owner == this);

  /**
   * The number (kieskringnummer) of this kieskring.
   */
  private /*@ spec_public @*/ byte my_number; //@ in objectState;
  //@ invariant 0 <= my_number;
  //@ invariant my_number <= CandidateList.MAX_KIESKRINGEN_PER_CANDIDATE_LIST;

  /**
   * The name (kieskringnaam) of this kieskring.
   *
   */
  private /*@ non_null spec_public @*/ String my_name; //@ in objectState;
  //@ invariant my_name.length() <= KIESKRING_NAME_MAX_LENGTH;
  //@ invariant my_name.owner == this;

  /**
   * The districts of this kieskring.
   */
  private final /*@ non_null spec_public @*/ District[] my_districts =
    new District [MAX_DISTRICTS_PER_KIESKRING + 1]; //@ in objectState;
  //@ maps my_districts[*] \into objectState;
  //@ invariant my_districts.length == MAX_DISTRICTS_PER_KIESKRING + 1;
  //@ invariant my_districts.owner == this;
  //@ invariant (\forall int i; 0 <= i && i < my_districts.length; my_districts[i].owner == this);

  /**
   * The number of districts in this kieskring.
   */
  private /*@ spec_public @*/ byte my_district_count; //@ in objectState;
  //@ invariant 0 <= my_district_count && my_district_count <= MAX_DISTRICTS_PER_KIESKRING;
  /*@ invariant my_district_count == (\sum int i; 0 <= i && i < my_districts.length;
    @                                (my_districts[i] != null) ? 1 : 0);
    @*/

  /**
   * The number of kieslijsten in this kieskring.
   */
  private /*@ spec_public @*/ byte my_kieslijst_count; //@ in objectState;
  //@ invariant 0 <= my_kieslijst_count && my_kieslijst_count <= MAX_KIESLIJSTEN_PER_KIESKRING;
  /*@ invariant my_kieslijst_count == (\sum int i; 0 <= i && i < my_kiesLijsten.length;
    @                                 (my_kiesLijsten[i] != null) ? 1 : 0);
    @*/


  // Constructors

  /**
   * Construct a new kieskring object given the specified
   * initialization values.
   *
   * <p> This method is private and not to be used by clients.
   * Instead, the factory method {@link #make(byte, java.lang.String)}
   * should be used. </p>
   *
   * @param a_kieskring_number the number of the new kieskring.
   * @param a_kieskring_name the name of the new kieskring.
   *
   * <pre><jml>
   * private normal_behavior
   *   requires 0 <= a_kieskring_number;
   *   requires a_kieskring_number <= CandidateList.MAX_KIESKRINGEN_PER_CANDIDATE_LIST;
   *   requires a_kieskring_name.length() <= KIESKRING_NAME_MAX_LENGTH;
   *   ensures number() == a_kieskring_number;
   *   ensures name().equals(a_kieskring_name);
   * </jml></pre>
   */
  private /*@ pure @*/ KiesKring(final byte a_kieskring_number,
                                 final /*@ non_null @*/ String a_kieskring_name) {
    my_number = a_kieskring_number;
    my_name = a_kieskring_name;
    //@ set my_name.owner = this;
  }

  /**
   * A factory method used to construct new kieskring objects.
   *
   * @param a_kieskring_number the number of the new kieskring.
   * @param a_kieskring_name the name of the new kieskring.
   * @return the new kieskring.
   *
   * <pre><jml>
   * normal_behavior
   *   requires 0 <= a_kieskring_number;
   *   requires a_kieskring_number <= CandidateList.MAX_KIESKRINGEN_PER_CANDIDATE_LIST;
   *   requires a_kieskring_name.length() <= KIESKRING_NAME_MAX_LENGTH;
   *   modifies \everything;
   *   ensures \result.number() == a_kieskring_number;
   *   ensures \result.name().equals(a_kieskring_name);
   * </jml></pre>
   */
  static /*@ non_null @*/ KiesKring make(final byte a_kieskring_number,
                                         final /*@ non_null @*/ String a_kieskring_name) {
    // Return cached version if it was already constructed.
    if (MY_CACHED_KIESKRINGEN[a_kieskring_number] != null) {
      if (MY_CACHED_KIESKRINGEN[a_kieskring_number].name().equals(a_kieskring_name)) {
        return MY_CACHED_KIESKRINGEN[a_kieskring_number];
      }
    }
    // Otherwise, construct a new instance, cache it, and return it.
    KiesKring result = new KiesKring(a_kieskring_number, a_kieskring_name);
    //@ set result.owner = MY_CACHED_KIESKRINGEN;
    MY_CACHED_KIESKRINGEN[a_kieskring_number] = result;
    return result;
  }


  // Accessors so that we can rely upon invariants and have pure data access.

  /**
   * @return the number of this kieskring.
   *
   * <pre><jml>
   * normal_behavior
   *   ensures 0 <= \result && \result <= CandidateList.MAX_KIESKRINGEN_PER_CANDIDATE_LIST;
   * </jml></pre>
   */
  /*@ pure @*/ byte number() {
    return my_number;
  }

  /**
   * @return the name of this kieskring.
   *
   * <pre><jml>
   * normal_behavior
   *   ensures \result.length() <= KIESKRING_NAME_MAX_LENGTH;
   * </jml></pre>
   */
  /*@ pure non_null @*/ String name() {
    return my_name;
  }


  // District support

  /**
   * Add a district to this kieskring.
   *
   * @param a_district the district to add.
   * @return <code>false</code> if this kieskring already contained
   * the given district; <code>true</code> if otherwise.
   *
   * <pre><jml>
   * normal_behavior
   *   requires !hasDistrict(a_district);
   *   modifies objectState;
   *   modifies a_district.owner;
   *   ensures hasDistrict(a_district);
   *   ensures \result <==> !\old(hasDistrict(a_district));
   *   ensures districtCount() == \old(districtCount() + 1);
   * also
   * normal_behavior
   *   requires hasDistrict(a_district);
   *   modifies \nothing;
   *   ensures !\result;
   * </jml></pre>
   */
  boolean addDistrict(final /*@ non_null @*/ District a_district) {
    if (hasDistrict(a_district)) {
      return false;
    }
    //@ set a_district.owner = this;
    my_districts[a_district.number()] = a_district;
    my_district_count++;
    return true;
  }

  /**
   * @return the districts of this kieskring.
   *
   * <pre><jml>
   * normal_behavior
   *   requires true;
   *   ensures \result == my_districts;
   *   ensures districtCount() == \old(districtCount());
   * </jml></pre>
   */
  /*@ pure @*/ District[] getDistricten() {
    return my_districts;
  }

  /**
   * @param a_district_number the number of the district to get.
   * @return the district in this kieskring with the given number.
   * A <code>null</code> is returned if no such district exists.
   *
   * <pre><jml>
   * normal_behavior
   *   requires 0 <= a_district_number && a_district_number <= MAX_DISTRICTS_PER_KIESKRING;
   *   ensures \result == my_districts[a_district_number];
   *   ensures districtCount() == \old(districtCount());
   * </jml></pre>
   */
  /*@ pure @*/ District getDistrict(final byte a_district_number) {
    return my_districts[a_district_number];
  }

  /**
   * @param a_district the district to check for.
   * @return a flag indicating if this kieskring contains the
   * specified district.
   *
   * <pre><jml>
   * normal_behavior
   *   ensures \result <==> (my_districts[a_district.number()] != null) &&
   *                        (my_districts[a_district.number()].equals(a_district));
   *   ensures districtCount() == \old(districtCount());
   * </jml></pre>
   */
  /*@ pure @*/ boolean hasDistrict(final /*@ non_null @*/ District a_district) {
    return (my_districts[a_district.number()] != null) &&
      (my_districts[a_district.number()].equals(a_district));
  }

  /**
   * @return the number of districts in this kieskring.
   *
   * <pre><jml>
   * normal_behavior
   *   ensures \result == my_district_count;
   *   implies_that
   *   ensures \result >= 0;
   * </jml></pre>
   */
  /*@ pure @*/ byte districtCount() {
    return my_district_count;
  }


  // KiesLijst support

  /**
   * Adds the specified kieslijst to this kieskring.
   *
   * @param a_kieslijst the kieslijst to add.
   * @return a flag indicating if the specified kieslijst was already
   * in this kieskring.
   *
   * <pre><jml>
   * normal_behavior
   *   requires hasKiesLijst(a_kieslijst);
   *   requires (* a_kieslijst.number() !?= KiesLijst.BLANCO; *);
   *   modifies \nothing;
   *   ensures !\result;
   * also
   * normal_behavior
   *   requires !hasKiesLijst(a_kieslijst);
   *   requires (* a_kieslijst.number() !?= KiesLijst.BLANCO; *);
   *   modifies objectState;
   *   modifies a_kieslijst.owner;
   *   ensures hasKiesLijst(a_kieslijst);
   *   ensures kieslijstCount() == \old(kieslijstCount() + 1);
   *   ensures \result;
   * </jml></pre>
   */
  boolean addKiesLijst(final /*@ non_null @*/ KiesLijst a_kieslijst) {
    if (hasKiesLijst(a_kieslijst)) {
      return false;
    }
    //@ set a_kieslijst.owner = this;
    my_kiesLijsten[a_kieslijst.number()] = a_kieslijst;
    my_kieslijst_count++;
    return true;
  }

  /**
   * @return the kieslijsten that have been added to this kieskring.
   *
   * <pre><jml>
   * normal_behavior
   *   requires true;
   *   ensures \result == my_kiesLijsten;
   *   ensures kieslijstCount() == \old(kieslijstCount());
   * </jml></pre>
   */
  /*@ pure @*/ KiesLijst[] getKiesLijsten() {
    return my_kiesLijsten;
  }

  /**
   * @param a_kieslijst_number the number of the kieslijst that we are
   * interested in.
   * @return the kieslijst represented by the specified kieslijst number.
   *
   * <pre><jml>
   * normal_behavior
   *   requires 0 <= a_kieslijst_number;
   *   requires a_kieslijst_number <= MAX_KIESLIJSTEN_PER_KIESKRING;
   *   ensures \result == my_kiesLijsten[a_kieslijst_number];
   *   ensures kieslijstCount() == \old(kieslijstCount());
   * </jml></pre>
   */
  /*@ pure @*/ KiesLijst getKiesLijst(final byte a_kieslijst_number) {
    return my_kiesLijsten[a_kieslijst_number];
  }

  /**
   * @param a_kieslijst the kieslijst that we wish to check for.
   * @return a flag indicating if this kieskring contains the specified
   * kieslijst.
   *
   * <pre><jml>
   * normal_behavior
   *   ensures \result <==> (my_kiesLijsten[a_kieslijst.number()] != null) &&
   *                        (my_kiesLijsten[a_kieslijst.number()].equals(a_kieslijst));
   *   ensures kieslijstCount() == \old(kieslijstCount());
   * </jml></pre>
   */
  /*@ pure @*/ boolean hasKiesLijst(final /*@ non_null @*/ KiesLijst a_kieslijst) {
    return (my_kiesLijsten[a_kieslijst.number()] != null) &&
      (my_kiesLijsten[a_kieslijst.number()].equals(a_kieslijst));
  }

  /**
   * @return the number of kieslijsten contained in this kieskring.
   *
   * <pre><jml>
   * normal_behavior
   *   ensures \result == my_kieslijst_count;
   *   implies_that
   *   ensures \result >= 0;
   * </jml></pre>
   */
  /*@ pure @*/ byte kieslijstCount() {
    return my_kieslijst_count;
  }

  /**
   * Clears all data in this <code>KiesKring</code> instance. In
   * particular, all district and kieslijsten references are cleared.
   *
   * <pre><jml>
   * normal_behavior
   *   modifies objectState;
   *   modifies MY_CACHED_KIESKRINGEN[*];
   *
   *   ensures my_number == 0;
   *   ensures my_name == "";
   *   ensures my_district_count == 0;
   *   ensures my_kieslijst_count == 0;
   *
   *   ensures (\forall int i; i < my_districts.length; my_districts[i] == null);
   *   ensures (\forall int i; i < my_kiesLijsten.length; my_kiesLijsten[i] == null);
   *   ensures (\forall int i; i < MY_CACHED_KIESKRINGEN.length;
   *                           MY_CACHED_KIESKRINGEN[i] == null);
   *
   *   ensures_redundantly number() == 0;
   *   ensures_redundantly name() == "";
   *   ensures_redundantly districtCount() == 0;
   *   ensures_redundantly kieslijstCount() == 0;
   * </jml></pre>
   */
  void clear() {
    my_number = 0;
    my_name = "";
    for (int i = 0; i < my_districts.length; i++) {
      if (my_districts[i] != null) {
        my_districts[i].clear();
        my_districts[i] = null;
      }
    }
    my_district_count = 0;
    for (int i = 0; i < my_kiesLijsten.length; i++) {
      if (my_kiesLijsten[i] != null) {
        my_kiesLijsten[i].clear();
        my_kiesLijsten[i] = null;
      }
    }
    my_kieslijst_count = 0;
    for (int i = 0; i < MY_CACHED_KIESKRINGEN.length; i++) {
      MY_CACHED_KIESKRINGEN[i] = null;
    }
  }


  // Implementation of Object

  /** {@inheritDoc} */
  public boolean equals(final Object an_object) {
    if (an_object == null) {
      return false;
    }

    if (!(an_object instanceof KiesKring)) {
      return false;
    }
    final KiesKring k = (KiesKring)an_object;

    return k.number() == number() &&
      k.name().equals(name()) &&
      k.my_districts.equals(my_districts);
  }

  /** {@inheritDoc} */
  public int hashCode() {
    return name().hashCode();
  }

  /** {@inheritDoc} */
  public String toString() {
    return number() + "." + (number() < 10 ? "  " : " ") + name();
  }


  // Implementation of Comparable

  /** {@inheritDoc} */
  public int compareTo(final Object an_object) {
    if (!(an_object instanceof KiesKring)) {
      throw new ClassCastException();
    }

    final KiesKring k = (KiesKring) an_object;
    return number() - k.number();
  } //@ nowarn Exception;
}
