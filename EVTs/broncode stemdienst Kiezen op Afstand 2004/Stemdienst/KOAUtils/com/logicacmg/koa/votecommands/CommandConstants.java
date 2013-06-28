/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.command.CommandConstants.java
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
  *  1.0		07-04-2003	KuijerM		First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.votecommands;
/**
 * Class containing all the constants for the commands.
 * 
 * @author: KuijerM
 */
public class CommandConstants
{
	/* context root for the web environment */
	public final static java.lang.String CONTEXT_PATH = "/KOAWeb";
	/* page used as default error JSP */
	public final static java.lang.String DEFAULT_ERROR_JSP = "/error.jsp";
	/* page used as default error JSP */
	public final static java.lang.String IDENTIFICATION_JSP =
		"/identification.jsp";
	/* the key used to store the requested command in the session */
	public final static java.lang.String COMMAND_IN_REQUEST_KEY = "COMMAND";
	public final static java.lang.String ERROR_IN_REQUEST_KEY = "ERROR";
	/* Constants for the links */
	public final static String LOGIN_ALIAS = "/Login";
	public final static String SELECT_CANDIDATE_ALIAS = "/KandidaatKeuze";
	public final static String COMMIT_CANDIDATE_ALIAS = "/BevestigKeuze";
	public final static String TXPAGE_ALIAS = "/Transactieoverzicht";
	public final static String ALREADY_VOTED_ALIAS = "/AlreadyVoted";
	public final static String STEMCODE = "STEMCODE";
	public final static String PASSWORD = "PASSWORD";
	public final static String KANDIDAATCODE = "KANDIDAATCODE";
	public final static String KANDIDAATCODE1 = "KANDIDAATCODE1";
	public final static String KANDIDAATCODE2 = "KANDIDAATCODE2";
	public final static String KANDIDAATCODE3 = "KANDIDAATCODE3";
	public final static String NAVIGATION_FIELD = "nav";
	public final static String NAVIGATION_PREVIOUS = "PREVIOUS";
	public final static String VOTE_INDICATION = "BEVESTIG";
	/**
	 * counter to hold the number of attempts that a kiezer tries to identify himself.
	 * This counter is only valid during the lifetime of a session !!
	 */
	public final static String LOGIN_ATTEMPTS = "attempts";
	/**
	 * counter to hold the number of attempts that a kiezer tries to
	 * vote for a candidate.
	 * This counter is only valid during the lifetime of a session !!
	 */
	public final static String VERIFY_CANDIDATE_ATTEMPTS =
		"verifycandidateattempts";
	//constant to indicate if a verification of the kiezer has failed
	public final static String KIEZER_LOGIN_FAILED = "kiezerloginfailed";
	public final static String KIEZER_OBJECT = "kiezerobj";
	public final static String INLOG_ERROR = "inlogerror";
}