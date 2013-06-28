/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.dataobjects.Kiezer.java
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
  * This dataclass contains data about a kiezer
  */
public class Kiezer implements java.io.Serializable
{
	public java.lang.String stemcode;
	public java.lang.String kieskringnummer;
	public java.lang.String districtnummer;
	public java.lang.Boolean reedsGestemd;
	public java.lang.Integer invalidLogins;
	public java.lang.Integer loginsAttempsLeft;
	public java.sql.Timestamp timeLastSuccesfullLogin;
	public java.lang.Boolean accountLocked;
	public java.sql.Timestamp timestampUnlock;
	public java.sql.Timestamp timestampGestemd;
	public java.lang.String modaliteit;
	public java.lang.String hashedWachtwooord;
	public java.lang.String kiezerIdentificatie;
	public java.lang.String wachtwoord;
	public java.lang.String transactionNumber;
}
