/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.command.KOACommandFactory.java
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
  *  1.0		07-04-2003	MKu			First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.voorzitter.command;
import java.util.Hashtable;

import com.logica.eplatform.command.NoSuchCommandException;
import com.logica.eplatform.command.http.HttpCommand;
import com.logica.eplatform.command.http.HttpCommandFactory;
import com.logica.eplatform.error.EPlatformException;
import com.logica.eplatform.util.LogHelper;
import com.logicacmg.koa.constants.ErrorConstants;
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
	private static com.logica.eplatform.command.http.HttpCommandFactory factory =
		null;
	/* hashtable used for the mapping of the servlet aliases to the commands */
	private java.util.Hashtable commandMapping = null;
	/**
	 * Private constructor for the command factory.
	 */
	private KOACommandFactory() throws ClassNotFoundException
	{
		LogHelper.log(
			LogHelper.INFO,
			"[KOACommandFactory] creating new CommandFactory...");
		/* fill the mapping hashtable with all the servlet-aliases and command classes */
		commandMapping = new Hashtable();
		commandMapping.put(
			"/Login",
			Class.forName("com.logicacmg.koa.voorzitter.command.LoginCommand"));
		commandMapping.put(
			"/GetCurrentState",
			Class.forName(
				"com.logicacmg.koa.voorzitter.command.GetCurrentStateCommand"));
		commandMapping.put(
			"/GetCurrentCounters",
			Class.forName(
				"com.logicacmg.koa.voorzitter.command.GetCurrentCounterCommand"));
		commandMapping.put(
			"/ChangeStateInitialize",
			Class.forName(
				"com.logicacmg.koa.voorzitter.command.statechange.InitializeCommand"));
		commandMapping.put(
			"/ChangeStateReInitialize",
			Class.forName(
				"com.logicacmg.koa.voorzitter.command.statechange.ReInitializeCommand"));
		commandMapping.put(
			"/ChangeStateOpen",
			Class.forName(
				"com.logicacmg.koa.voorzitter.command.statechange.OpenCommand"));
		commandMapping.put(
			"/ChangeStateClose",
			Class.forName(
				"com.logicacmg.koa.voorzitter.command.statechange.CloseCommand"));
		commandMapping.put(
			"/ChangeStateSuspend",
			Class.forName(
				"com.logicacmg.koa.voorzitter.command.statechange.SuspendCommand"));
		commandMapping.put(
			"/ChangeStatePrepareVoteCount",
			Class.forName(
				"com.logicacmg.koa.voorzitter.command.statechange.PrepareVoteCountCommand"));
		commandMapping.put(
			"/ChangeStateCountVote",
			Class.forName(
				"com.logicacmg.koa.voorzitter.command.statechange.CountVoteCommand"));
		commandMapping.put(
			"/ChangeStatePrepare",
			Class.forName(
				"com.logicacmg.koa.voorzitter.command.statechange.PrepareCommand"));
		commandMapping.put(
			"/Index",
			Class.forName(
				"com.logicacmg.koa.voorzitter.command.IndexPaginaCommand"));
		commandMapping.put(
			"/Report",
			Class.forName(
				"com.logicacmg.koa.reportserver.command.KOAReportCommand"));
		commandMapping.put(
			"/CompareFingerprints",
			Class.forName(
				"com.logicacmg.koa.voorzitter.command.CompareKieslijstFingerprints"));
		commandMapping.put(
			"/ShowReports",
			Class.forName(
				"com.logicacmg.koa.voorzitter.command.ShowReportsCommand"));
		commandMapping.put(
			"/FetchData",
			Class.forName(
				"com.logicacmg.koa.voorzitter.command.FetchDataCommand"));
		commandMapping.put(
			"/SelectProcesVerbaal",
			Class.forName(
				"com.logicacmg.koa.voorzitter.command.SelectProcesVerbaalCommand"));
		LogHelper.log(
			LogHelper.INFO,
			"[KOACommandFactory] new CommandFactory created");
	}
	/**
	 * Retrieve the command from the HTTP request
	 * 
	 * @param HttpServletRequest	Object that encapsulates the request to the servlet
	 * 
	 * @return HttpCommand 			The command that corresponds to the servlet alias
	 */
	public HttpCommand getCommand(HttpServletRequest request)
		throws NoSuchCommandException
	{
		HttpCommand command = null;
		/* get the servlet alias from the request */
		String alias = request.getServletPath();
		LogHelper.trace(
			LogHelper.TRACE,
			"[KOACommandFactory] getCommand with command alias ["
				+ alias
				+ "]");
		/* determine command from alias */
		Class commandClass = (Class) commandMapping.get(alias);
		if (commandClass == null)
		{
			/* if the alias is not present, log the warning and throw a noSuchCommandException */
			LogHelper.log(
				LogHelper.WARNING,
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
			LogHelper.log(
				LogHelper.ERROR,
				"[KOACommandFactory] EPlatformException " + ep.getMessage());
			throw new NoSuchCommandException(ep.getErrorCode());
		}
		catch (Exception e)
		{
			/* if an exception occures, throw a new noSuchCommandException and log the error  */
			LogHelper.log(LogHelper.ERROR, "CommandFactory getCommand()");
			throw new NoSuchCommandException(ErrorConstants.DEFAULT);
		}
		/* return the command after it is initialized */
		return command;
	}
	/**
	 * Singleton getter for the command factory.
	 * 
	 * @return HttpCommandFactory The KOA command factory
	 */
	public static HttpCommandFactory getHttpCommandFactory()
	{
		LogHelper.log(
			LogHelper.TRACE,
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