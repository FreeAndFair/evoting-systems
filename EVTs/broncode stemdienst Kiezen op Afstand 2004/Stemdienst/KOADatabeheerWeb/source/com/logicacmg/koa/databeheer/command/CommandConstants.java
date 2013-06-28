/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.command.databeheer.CommandConstants.java
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
  *  1.0		11-04-2003	MRo		First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.databeheer.command;
/**
 * Class containing all the constants for the commands.
 * 
 * @author: KuijerM
 */
public class CommandConstants
{
	/* context root for the web environment */
	final static java.lang.String CONTEXT_PATH = "/KOADatabeheerWeb";
	/* page used as default error JSP */
	final static java.lang.String DEFAULT_ERROR_JSP = "/error.jsp";
	/* the key used to store the requested command in the session */
	public final static java.lang.String COMMAND_IN_REQUEST_KEY = "COMMAND";
	// the key used to store information in the command 
	public final static String UPLOAD_SESSION = "UPLOAD_SESSION";
	public final static String UPLOAD_ACTION = "action";
	public final static String UPLOAD_CONTENTTYPE = "contenttype";
	public final static String UPLOAD_KIESLIJST = "kieslijst";
	public final static String UPLOAD_DELETE = "delete";
	public final static String UPLOAD_KIEZER_COUNT = "kiezercount";
	public final static String UPLOAD_KIEZER = "kiezer";
	public final static String UPLOAD_REQUEST_REFERENCE = "requestreference";
	public final static String UPLOAD_CREATIONTIME = "creationtime";
	public final static String UPLOAD_KIESKRING_COUNT = "kieskringcount";
	public final static String UPLOAD_DISTRICT_COUNT = "districtcount";
	public final static String UPLOAD_KIESLIJST_COUNT = "kieslijstcount";
	public final static String UPLOAD_POSITIE_COUNT = "positiecount";
	public final static String UPLOAD_KIESKRING = "kieskring";
	public final static String UPLOAD_DISTRICT = "district";
	public final static String UPLOAD_POSITIE = "positie";
	public final static String UPLOAP_CONTENTTYPE_VALUE_KIEZERSLIJST =
		"kiezersregister";
	public final static String UPLOAP_CONTENTTYPE_VALUE_KIESLIJST = "kieslijst";
	/* the admin object in the session */
	public final static java.lang.String ADMIN_OBJECT_IN_SESSION =
		"ADMIN_OBJECT_IN_SESSION";
}