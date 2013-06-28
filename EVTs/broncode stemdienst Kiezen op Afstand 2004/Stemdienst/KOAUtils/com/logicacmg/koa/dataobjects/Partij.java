/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.dataobjects.Partij.java
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
  *  0.1		18-04-2003	AGr			First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.dataobjects;
/**
 * Datacalss contains data about a partij (kieslijst)
 */
public class Partij implements java.io.Serializable
{
	public String naam;
	public String kieslijstnummer;
	public String kieskringnummer;
}
