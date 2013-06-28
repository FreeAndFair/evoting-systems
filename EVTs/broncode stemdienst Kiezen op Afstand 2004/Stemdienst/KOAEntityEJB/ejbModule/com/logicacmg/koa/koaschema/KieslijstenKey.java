package com.logicacmg.koa.koaschema;
/**
 * Key class for Entity Bean: Kieslijsten
 */
public class KieslijstenKey implements java.io.Serializable
{
	static final long serialVersionUID = 3206093459760846163L;
	/**
	 * Implemetation field for persistent attribute: kieslijstnummer
	 */
	public java.lang.String kieslijstnummer;
	/**
	 * Implemetation field for persistent attribute: fk_kkr_1_kieskringnummer
	 */
	public java.lang.String fk_kkr_1_kieskringnummer;
	/**
	 * Creates an empty key for Entity Bean: Kieslijsten
	 */
	public KieslijstenKey()
	{
	}
	/**
	 * Creates a key for Entity Bean: Kieslijsten
	 */
	public KieslijstenKey(
		java.lang.String kieslijstnummer,
		com.logicacmg.koa.koaschema.KieskringenKey argFk_kkr_1)
	{
		this.kieslijstnummer = kieslijstnummer;
		privateSetFk_kkr_1Key(argFk_kkr_1);
	}
	/**
	 * Returns true if both keys are equal.
	 */
	public boolean equals(java.lang.Object otherKey)
	{
		if (otherKey instanceof com.logicacmg.koa.koaschema.KieslijstenKey)
		{
			com.logicacmg.koa.koaschema.KieslijstenKey o =
				(com.logicacmg.koa.koaschema.KieslijstenKey) otherKey;
			return (
				(this.kieslijstnummer.equals(o.kieslijstnummer))
					&& (this
						.fk_kkr_1_kieskringnummer
						.equals(o.fk_kkr_1_kieskringnummer)));
		}
		return false;
	}
	/**
	 * Returns the hash code for the key.
	 */
	public int hashCode()
	{
		return (
			kieslijstnummer.hashCode() + fk_kkr_1_kieskringnummer.hashCode());
	}
	/**
	 * This method was generated for supporting the association named fk_kkr_1.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public com.logicacmg.koa.koaschema.KieskringenKey getFk_kkr_1Key()
	{
		com.logicacmg.koa.koaschema.KieskringenKey temp =
			new com.logicacmg.koa.koaschema.KieskringenKey();
		boolean fk_kkr_1_NULLTEST = true;
		fk_kkr_1_NULLTEST &= (fk_kkr_1_kieskringnummer == null);
		temp.kieskringnummer = fk_kkr_1_kieskringnummer;
		if (fk_kkr_1_NULLTEST)
			temp = null;
		return temp;
	}
	/**
	 * This method was generated for supporting the association named fk_kkr_1.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public void privateSetFk_kkr_1Key(
		com.logicacmg.koa.koaschema.KieskringenKey inKey)
	{
		boolean fk_kkr_1_NULLTEST = (inKey == null);
		fk_kkr_1_kieskringnummer =
			(fk_kkr_1_NULLTEST) ? null : inKey.kieskringnummer;
	}
}
