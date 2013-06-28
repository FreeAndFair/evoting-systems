/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.dataobjects.Stem.java
  *
  * -----------------------------------------------------------------------
  * 
  *  (c) 2003  Ministerie van Binnenlandse Zaken en Koninkrijkrelaties
  *
  *  Project		: Kiezen Op Afstand (KOA)
  *  Project Number	: ECF-2651
  *  
  *  History:
  *  Version	Date		Name		Reason
  * ---------------------------------------------------------
  *  0.1		17-04-2003	AGr			First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.dataobjects;
import java.util.Vector;
import java.io.Serializable;
/**
 *  This class contains uncrypted vote data. The fields are related to a kandidaat.
 */
public class Kandidaat implements java.io.Serializable
{
	public String achterNaam;
	public String roepNaam;
	public String voorletters;
	public char geslacht;
	public String woonplaats;
	public String kieskringnummer;
	public String kieslijstnummer;
	public String positienummer;
	public Vector kandidaatcodes;
	public String districtnummer;
	public String lijstnaam;
}
