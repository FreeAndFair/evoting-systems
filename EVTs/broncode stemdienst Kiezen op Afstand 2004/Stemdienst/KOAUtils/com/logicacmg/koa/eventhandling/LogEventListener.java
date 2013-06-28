/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.eventhandling.LogEventListener.java
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
  *  0.1		07-04-2003	KuijerM		First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.eventhandling;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.Hashtable;
import java.util.Properties;

import javax.naming.InitialContext;
import javax.naming.NamingException;
import javax.rmi.PortableRemoteObject;

import com.logica.eplatform.eventhandling.Event;
import com.logica.eplatform.eventhandling.EventListener;
import com.logica.eplatform.eventhandling.EventListenerContext;
import com.logica.eplatform.services.logging.LogService;
import com.logica.eplatform.util.LogHelper;
import com.logicacmg.koa.eventhandling.KOAEvent;
import com.logicacmg.koa.utils.KOALogHelper;
/**
 * This Implementation logs events to the LogService from the Services Framework.
 * 
 * @author: KuijerM
 */
public class LogEventListener implements EventListener
{
	private LogService logService;
	private static int DEFAULT_MINLEVEL = -1;
	private static int DEFAULT_MAXLEVEL = 6;
	private int minLevel = DEFAULT_MINLEVEL;
	private int maxLevel = DEFAULT_MAXLEVEL;
	private String serviceName = null;
	private boolean bIsDebugMode = false;
	/**
	 * constructor for the event listener
	 * 
	 */
	public LogEventListener()
	{
		System.out.println("[LogEventListener] Starting LogEventListener");
	}
	/**
	 * Bind the logservice to the event listener
	 * The logservice logs to a file.
	 */
	private void bindLogService()
	{
		System.out.println(
			"[LogEventListener.bindLogService] Start binding log service");
		try
		{
			InitialContext icContext = this.initInitialContext();
			Object obj = icContext.lookup(serviceName);
			logService =
				(LogService) PortableRemoteObject.narrow(obj, LogService.class);
			System.out.println(
				"[LogEventListener.bindLogService] Service binded succesfully...");
		}
		catch (NamingException ne)
		{
			System.err.println(
				"[LogEventListener.bindLogService] Could not find log service in registry with JNDI name "
					+ serviceName);
			ne.printStackTrace();
		}
		catch (Exception e)
		{
			System.err.println(
				"[LogEventListener.bindLogService] Error occured during lookup service");
			e.printStackTrace();
		}
	}
	private InitialContext initInitialContext()
	{
		/* init variables */
		InitialContext icContext = null;
		Properties props = new Properties();
		try
		{
			/* load the properties */
			props.load(
				this.getClass().getResourceAsStream("/services.properties"));
		}
		catch (java.io.IOException ioe)
		{
			System.err.println(
				"[LogEventListener.initInitialContext] Cannot load service.properties");
			return icContext;
		}
		try
		{
			Hashtable htProps = new Hashtable();
			htProps.put(
				javax.naming.Context.PROVIDER_URL,
				props.getProperty("context.provider"));
			htProps.put(
				javax.naming.Context.INITIAL_CONTEXT_FACTORY,
				props.getProperty("context.factory"));
			icContext = new InitialContext(htProps);
		}
		catch (NamingException ne)
		{
			System.err.println(
				"[LogEventListener.initInitialContext] Cannot load initial context");
			return icContext;
		}
		return icContext;
	}
	/**
	 * initialize the event listener with the parameters from the properties
	 * if no parameters are specified the default parameters are used.
	 * 
	 * @param elc The context of the eventlistener containing the parameters
	 */
	public void init(EventListenerContext elc)
	{
		try
		{
			/* try to get the minimum log level */
			minLevel = Integer.parseInt((String) elc.getProperty("minlevel"));
		}
		catch (NumberFormatException nfe)
		{
			/* if no proper minimum level can be found, use the default. */
			System.out.println(
				"[LogEventListener] No proper minlevel specified, default used.");
		}
		try
		{
			/* try to get the maximum log level */
			maxLevel = Integer.parseInt((String) elc.getProperty("maxlevel"));
		}
		catch (NumberFormatException nfe)
		{
			/* if no proper maximum level can be found, use the default. */
			System.out.println(
				"[LogEventListener] No proper maxlevel specified, default used.");
		}
		try
		{
			/* try to get the service name */
			serviceName = elc.getProperty("serviceName");
			/* check if we have a service name */
			if (serviceName == null)
			{
				/* if we dont have a service name, log a message we dont bind the service */
				System.err.println(
					"[LogEventListener.init] No servicename found, cannot bind service...");
			}
			else
			{
				System.out.println(
					"[LogEventListener.init] Found servicename "
						+ serviceName
						+ ", start binding service...");
				/* if we have a service name, bind the service */
				this.bindLogService();
			}
		}
		catch (Exception e)
		{
			/* if no proper service name can be found, use the default. */
			LogHelper.log(
				LogHelper.WARNING,
				"[LogEventListener] No serviceName set. default used");
		}
		/* check if it is in debug mode */
		bIsDebugMode = com.logicacmg.koa.constants.TechnicalProps.isDebugMode();
	}
	/**
	 * The on log event event handling.
	 * Logs the incoming event, if it is between the minimum and maximum severity
	 * If it is an error it is logged to the standard error, else it is 
	 * logged to the standard out.
	 * 
	 * @param event The event to log
	 */
	public void onEvent(Event event)
	{
		/* check if the event should be logged by this event listener */
		if ((event.getSeverity() >= minLevel)
			&& (event.getSeverity() <= maxLevel))
		{
			try
			{
				String sMessage = event.getMessage();
				if (event instanceof KOAEvent)
				{
					KOAEvent koaEvent = (KOAEvent) event;
					if (koaEvent.getActor() != null)
					{
						sMessage =
							"["
								+ ((KOAEvent) event).getActor()
								+ "]"
								+ sMessage;
					}
					if (koaEvent.getException() != null)
					{
						StringWriter sw = new StringWriter();
						PrintWriter pw = new PrintWriter(sw);
						koaEvent.getException().printStackTrace(pw);
						sMessage = sMessage + "\n" + sw.toString();
					}
				}
				/* log the message */
				logService.log(sMessage);
				/* in debug also log to the console */
				if (bIsDebugMode)
				{
					if (event.getSeverity() == KOALogHelper.ERROR)
					{
						System.err.println(sMessage);
					}
					else
					{
						System.out.println(sMessage);
					}
				}
			}
			/* if something goes wrong, try one more time to log it to the proper output */
			catch (Exception e)
			{
				try
				{
					/* try to log again */
					logService.log(event.getMessage());
					System.out.println(event.getMessage());
					e.printStackTrace();
				}
				/* if we fail again try to log an error */
				catch (Exception ex)
				{
					System.err.println(
						"[LogEventListener] [ERROR] "
							+ ex.getClass().getName()
							+ " while logging to logService: "
							+ ex.getMessage());
					System.err.println(
						"[LogEventListener] [ORIGINAL LOGMESSAGE] "
							+ event.getMessage());
				}
			}
		}
	}
}