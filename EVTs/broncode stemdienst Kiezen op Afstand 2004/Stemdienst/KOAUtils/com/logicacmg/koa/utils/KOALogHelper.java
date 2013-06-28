/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.utils.KOALogHelper.java
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
  *  0.1		23-04-2003	MKu			First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.utils;
import com.logica.eplatform.error.ErrorMessageFactory;
import com.logica.eplatform.eventhandling.EventHandler;
import com.logicacmg.koa.eventhandling.KOAEvent;
/**
 * Loghelper implementation for the KOA project.
 * This LogHelper extends the e-Platform loghelper.
 * This extension is used to provide stacktrace information
 * if provided.
 * 
 * @author KuijerM
 */
public class KOALogHelper implements java.io.Serializable
{
	public final static int FATAL = 1;
	public final static int ERROR = 2;
	public final static int WARNING = 3;
	public final static int INFO = 4;
	public final static int TRACE = 5;
	/**
	 * Logs the logmessage with the specified log level 
	 * and adds the throwable stacktrace to the message.
	 * 
	 * @param int		 The loglevel
	 * @param String	 The message to log
	 * 
	 */
	public static void log(int iLevel, String sMessage)
	{
		/* create new event and let the eventhandler handle the event */
		KOAEvent event = new KOAEvent(sMessage, iLevel);
		EventHandler.handleEvent(event, "LOG");
	}
	/**
	 * Logs an ERROR logmessage 
	 * and adds the throwable stacktrace to the db
	 * 
	 * @param String 	The actor that initialized the logging.
	 * @param String	The message to log
	 * @param Throwable The exception that occurred
	 */
	public static void logError(String sActor, String sMessage, Throwable t)
	{
		/* create new event and let the eventhandler handle the event */
		KOAEvent event = new KOAEvent(sMessage, KOALogHelper.ERROR, sActor, t);
		EventHandler.handleEvent(event, "LOG");
	}
	/**
	 * Logs an ERROR logmessage based on the specified logerror code
	 * and adds the throwable stacktrace to the db
	 * 
	 * @param String  	The actor that initialized the logging.
	 * @param String  	The error code to map to the message in the error message factory
	 * @param Throwable The exception that occurred
	 */
	public static void logErrorCode(
		String sActor,
		String sErrorCode,
		Throwable t)
	{
		KOALogHelper.logErrorCode(sActor, sErrorCode, null, t);
	}
	/**
	 * Logs an ERROR logmessage based on the specified logerror code
	 * and adds the throwable stacktrace to the db
	 * 
	 * @param String 	The actor that initialized the logging.
	 * @param String 	The error code to map to the message in the error message factory
	 * @param String[] 	The parameters for the error code
	 * @param Throwable The exception that occurred
	 * 
	 */
	public static void logErrorCode(
		String sActor,
		String sErrorCode,
		String[] params,
		Throwable t)
	{
		String sMessage = null;
		try
		{
			sMessage =
				"Message with errorcode ["
					+ sErrorCode
					+ "]  "
					+ ErrorMessageFactory
						.getErrorMessageFactory()
						.getErrorMessage(
						sErrorCode,
						params);
		}
		catch (java.io.IOException ioe)
		{
			sMessage =
				"IO exception when getting message from Error Message factory with error code : "
					+ sErrorCode;
		}
		KOALogHelper.logError(sActor, sMessage, t);
	}
	/**
	 * Logs an FATAL logmessage 
	 * and adds the throwable stacktrace to the db
	 * 
	 * @param String 	The actor that initialized the logging.
	 * @param String 	The message to log
	 * @param Throwable The exception that occurred
	 * 
	 */
	public static void logFatal(String sActor, String sMessage, Throwable t)
	{
		/* create new event and let the eventhandler handle the event */
		KOAEvent event = new KOAEvent(sMessage, KOALogHelper.FATAL, sActor, t);
		EventHandler.handleEvent(event, "LOG");
	}
	/** 
	 * Logs the audit message with the specified log level 
	 * 
	 * @param int 	 	The loglevel
	 * @param String 	The action which is taking place
	 * @param String 	The component performing the action	
	 * @param String 	The initializer of the audit.
	 * @param sMessage 	The message to log
	 */
	public static void audit(
		int iLevel,
		String sAction,
		String sComponent,
		String sActor,
		String sMessage)
	{
		/* create new event and let the eventhandler handle the event */
		KOAEvent event =
			new KOAEvent(sMessage, iLevel, sAction, sComponent, sActor);
		EventHandler.handleEvent(event, "AUDIT");
	}
	/** 
	 * Logs the audit message with the specified log level in a transaction 
	 * 
	 * @param int 	 	The loglevel
	 * @param String 	The action which is taking place
	 * @param String 	The component performing the action	
	 * @param String 	The initializer of the audit.
	 * @param sMessage 	The message to log
	 */
	public static void auditTX(
		int iLevel,
		String sAction,
		String sComponent,
		String sActor,
		String sMessage)
	{
		/* create new event and let the eventhandler handle the event */
		KOAEvent event =
			new KOAEvent(sMessage, iLevel, sAction, sComponent, sActor);
		EventHandler.handleEvent(event, "AUDIT_TX");
	}
	/**
	 * Translates the Type for the int value
	 * 
	 * @param int The type to get the translation for
	 * 
	 * @return String the translation
	 */
	public static String getTypeForInt(int iType)
	{
		String sResult = "Onbekend type";
		switch (iType)
		{
			case FATAL :
				sResult = "F F"; //"Fatale fout";
				break;
			case ERROR :
				sResult = "F"; //"Fout";
				break;
			case WARNING :
				sResult = "W"; //"Waarschuwing";
				break;
			case INFO :
				sResult = "I"; //"Informatie";
				break;
			case TRACE :
				sResult = "I"; //"Informatie";
				break;
		}
		return sResult;
	}
}