/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.databeheer.command.KOACommandFactory.java
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
import java.util.Hashtable;

import com.logica.eplatform.command.NoSuchCommandException;
import com.logica.eplatform.command.http.HttpCommand;
import com.logica.eplatform.command.http.HttpCommandFactory;
import com.logica.eplatform.error.EPlatformException;
import com.logicacmg.koa.utils.KOALogHelper;
/**
 * Factory to create the commands, based on the requested CommandClass
 * via the alias through the servlet.
 * 
 * @author: KuijerM
 */
public class KOACommandFactory
	implements com.logica.eplatform.command.http.HttpCommandFactory
{
	/* the singleton instance of the command factory */
	private static com.logica.eplatform.command.http.HttpCommandFactory factory;
	/* hashtable used for the mapping of the servlet aliases to the commands */
	private java.util.Hashtable commandMapping;
	/**
	 * Private constructor for the command factory.
	 * Creation date: (07-04-2003 14:07:30)
	 */
	private KOACommandFactory() throws ClassNotFoundException
	{
		KOALogHelper.log(
			KOALogHelper.INFO,
			"[KOACommandFactory] new CommandFactory created");
		/* fill the mapping hashtable with all the servlet-aliases and command classes */
		commandMapping = new Hashtable();
		commandMapping.put(
			"/Login",
			Class.forName("com.logicacmg.koa.databeheer.command.LoginCommand"));
		commandMapping.put(
			"/ScheduledJobsOverview",
			Class.forName(
				"com.logicacmg.koa.databeheer.command.ScheduledJobsAdministrationCommand"));
		commandMapping.put(
			"/JobTypesOverview",
			Class.forName(
				"com.logicacmg.koa.databeheer.command.JobTypesAdministrationCommand"));
		commandMapping.put(
			"/UploadKieslijst",
			Class.forName("com.logicacmg.koa.databeheer.command.Upload"));
		commandMapping.put(
			"/UploadKRRemove",
			Class.forName("com.logicacmg.koa.databeheer.command.Upload"));
		commandMapping.put(
			"/UploadKRUpdate",
			Class.forName("com.logicacmg.koa.databeheer.command.Upload"));
		commandMapping.put(
			"/UploadKRReplace",
			Class.forName("com.logicacmg.koa.databeheer.command.Upload"));
		commandMapping.put(
			"/ProcessUpload",
			Class.forName(
				"com.logicacmg.koa.databeheer.command.ProcessUpload"));
		commandMapping.put(
			"/SelectExport",
			Class.forName(
				"com.logicacmg.koa.databeheer.command.SelectExportCommand"));
		commandMapping.put(
			"/Report",
			Class.forName(
				"com.logicacmg.koa.reportserver.command.KOAReportCommand"));
		commandMapping.put(
			"/SelectUpload",
			Class.forName(
				"com.logicacmg.koa.databeheer.command.SelectUploadCommand"));
	}
	/**
	 * Insert the method's description here.
	 * Creation date: (07-04-2003 14:07:30)
	 * @param request The current request for this action
	 * @return HttpCommand The command that corresponds to the servlet alias
	 */
	public HttpCommand getCommand(HttpServletRequest request)
		throws NoSuchCommandException
	{
		HttpCommand command = null;
		/* get the servlet alias from the request */
		String alias = request.getServletPath();
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[KOACommandFactory] getCommand with command alias ["
				+ alias
				+ "]");
		/* determine command from alias */
		Class commandClass = (Class) commandMapping.get(alias);
		if (commandClass == null)
		{
			/* if the alias is not present, log the warning and throw a noSuchCommandException */
			KOALogHelper.log(
				KOALogHelper.WARNING,
				"CommandClass was null for alias: " + alias);
			throw new NoSuchCommandException();
		}
		try
		{
			/* create a new instance of the command class */
			command = (HttpCommand) commandClass.newInstance();
			/* execute the init on the Http command with the current request as a parameter */
			command.init(request);
		}
		catch (EPlatformException ep)
		{
			/* if an eplatform exception occures, throw a new noSuchCommandException and log the error  */
			KOALogHelper.log(
				KOALogHelper.ERROR,
				"[KOACommandFactory] EPlatformException " + ep.getMessage());
			throw new NoSuchCommandException(ep.getErrorCode());
		}
		catch (Exception e)
		{
			/* if an exception occures, throw a new noSuchCommandException and log the error  */
			KOALogHelper.log(KOALogHelper.ERROR, "CommandFactory getCommand()");
			throw new NoSuchCommandException("default");
		}
		/* return the command after it is initialized */
		return command;
	}
	/**
	 * Singleton getter for the command factory.
	 * Creation date: (20-2-2001 12:55:12)
	 * @return HttpCommandFactory The KOA command factory
	 */
	public static HttpCommandFactory getHttpCommandFactory()
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[KOACommandFactory] getHttpCommandFactory");
		/* Return the Command factory as a singleton */
		if (factory == null)
		{
			try
			{
				/* if we dont have a command factory yet, create one */
				factory = new KOACommandFactory();
			}
			catch (ClassNotFoundException cnfe)
			{
				/* if we cant find the command factory class, throw a runtime exception */
				throw new RuntimeException(
					"Error creating CommandFactory: " + cnfe.getMessage());
			}
		}
		/* return the singleton instance */
		return factory;
	}
}