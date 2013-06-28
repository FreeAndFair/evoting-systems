package com.logicacmg.koa.koaschema;
/**
 * Key class for Entity Bean: Lijstposities
 */
public class LijstpositiesKey implements java.io.Serializable
{
	static final long serialVersionUID = 3206093459760846163L;
	/**
	 * Implemetation field for persistent attribute: positienummer
	 */
	public java.lang.String positienummer;
	/**
	 * Implemetation field for persistent attribute: fk_klkr_1_kieslijstnummer
	 */
	public java.lang.String fk_klkr_1_kieslijstnummer;
	/**
	 * Implemetation field for persistent attribute: fk_klkr_1_fk_kkr_1_kieskringnummer
	 */
	public java.lang.String fk_klkr_1_fk_kkr_1_kieskringnummer;
	/**
	 * Creates an empty key for Entity Bean: Lijstposities
	 */
	public LijstpositiesKey()
	{
	}
	/**
	 * Creates a key for Entity Bean: Lijstposities
	 */
	public LijstpositiesKey(
		java.lang.String positienummer,
		com.logicacmg.koa.koaschema.KieslijstenKey argFk_klkr_1)
	{
		this.positienummer = positienummer;
		privateSetFk_klkr_1Key(argFk_klkr_1);
	}
	/**
	 * Returns true if both keys are equal.
	 */
	public boolean equals(java.lang.Object otherKey)
	{
		if (otherKey instanceof com.logicacmg.koa.koaschema.LijstpositiesKey)
		{
			com.logicacmg.koa.koaschema.LijstpositiesKey o =
				(com.logicacmg.koa.koaschema.LijstpositiesKey) otherKey;
			return (
				(this.positienummer.equals(o.positienummer))
					&& (this
						.fk_klkr_1_kieslijstnummer
						.equals(o.fk_klkr_1_kieslijstnummer))
					&& (this
						.fk_klkr_1_fk_kkr_1_kieskringnummer
						.equals(o.fk_klkr_1_fk_kkr_1_kieskringnummer)));
		}
		return false;
	}
	/**
	 * Returns the hash code for the key.
	 */
	public int hashCode()
	{
		return (
			positienummer.hashCode()
				+ fk_klkr_1_kieslijstnummer.hashCode()
				+ fk_klkr_1_fk_kkr_1_kieskringnummer.hashCode());
	}
	/**
	 * This method was generated for supporting the association named fk_klkr_1.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public com.logicacmg.koa.koaschema.KieslijstenKey getFk_klkr_1Key()
	{
		com.logicacmg.koa.koaschema.KieslijstenKey temp =
			new com.logicacmg.koa.koaschema.KieslijstenKey();
		boolean fk_klkr_1_NULLTEST = true;
		fk_klkr_1_NULLTEST &= (fk_klkr_1_kieslijstnummer == null);
		temp.kieslijstnummer = fk_klkr_1_kieslijstnummer;
		fk_klkr_1_NULLTEST &= (fk_klkr_1_fk_kkr_1_kieskringnummer == null);
		temp.fk_kkr_1_kieskringnummer = fk_klkr_1_fk_kkr_1_kieskringnummer;
		if (fk_klkr_1_NULLTEST)
			temp = null;
		return temp;
	}
	/**
	 * This method was generated for supporting the association named fk_klkr_1.
	 * It will be deleted/edited when the association is deleted/edited.
	 */
	public void privateSetFk_klkr_1Key(
		com.logicacmg.koa.koaschema.KieslijstenKey inKey)
	{
		boolean fk_klkr_1_NULLTEST = (inKey == null);
		fk_klkr_1_kieslijstnummer =
			(fk_klkr_1_NULLTEST) ? null : inKey.kieslijstnummer;
		fk_klkr_1_fk_kkr_1_kieskringnummer =
			(fk_klkr_1_NULLTEST) ? null : inKey.fk_kkr_1_kieskringnummer;
	}
}
