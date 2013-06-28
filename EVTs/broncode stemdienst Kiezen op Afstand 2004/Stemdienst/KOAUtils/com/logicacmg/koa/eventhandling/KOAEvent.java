/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.eventhandling.KOAEvent.java
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
package com.logicacmg.koa.eventhandling;
import com.logica.eplatform.eventhandling.DefaultEvent;
/**
 * Event used as extension to the e-platform DefaultEvent
 * The purpose of this extension is to include stacktrace
 * information.
 * 
 * @author KuijerM
 */
public class KOAEvent extends DefaultEvent
{
	/**
	 * The full message including the throwable stacktrace
	 * 
	 */
	private String g_sFullMessage = null;
	/**
	 * The component in which this action has started
	 * 
	 */
	private String g_sComponent = null;
	/**
	 * The actor that initialized this event
	 * 
	 */
	private String g_sActor = null;
	/**
	 * The action that initialized this event
	 * 
	 */
	private String g_sAction = null;
	/**
	 * The exception for this event
	 * 
	 */
	private Throwable g_tThrowable = null;
	/**
	 * Constructor for the KOAEvent
	 * 
	 * @param sMessage The message to use in the event
	 * @param iSeverity The severity of the event
	 */
	public KOAEvent(String sMessage, int iSeverity)
	{
		this(sMessage, iSeverity, null, null, null, null);
	}
	/**
	 * Constructor for the KOAEvent
	 * 
	 * @param sMessage The message to use in the event
	 * @param iSeverity The severity of the event
	 * @param sComponent The component that initialized this event.
	 * 
	 */
	public KOAEvent(
		String sMessage,
		int iSeverity,
		String sAction,
		String sComponent)
	{
		this(sMessage, iSeverity, sAction, sComponent, null, null);
	}
	/**
	 * Constructor for the KOAEvent
	 * 
	 * @param sMessage The message to use in the event
	 * @param iSeverity The severity of the event
	 * @param sAction The action that inits the event
	 * @param sComponent The component that initialized this event.
	 * @param sActor The initiator that initialized this event.
	 * 
	 */
	public KOAEvent(
		String sMessage,
		int iSeverity,
		String sAction,
		String sComponent,
		String sActor)
	{
		this(sMessage, iSeverity, sAction, sComponent, sActor, null);
	}
	/**
	 * Constructor for the KOAEvent
	 * 
	 * @param sMessage The message to use in the event
	 * @param iSeverity The severity of the event
	 * @param throwable The throwable (exception) for this event. Can be null.
	 * 
	 */
	public KOAEvent(String sMessage, int iSeverity, Throwable throwable)
	{
		this(sMessage, iSeverity, null, null, null, throwable);
	}
	/**
	 * Constructor for the KOAEvent
	 * 
	 * @param sMessage The message to use in the event
	 * @param iSeverity The severity of the event
	 * @param sAction The action that inits the event
	 * @param throwable The throwable (exception) for this event. Can be null.
	 * 
	 */
	public KOAEvent(
		String sMessage,
		int iSeverity,
		String sAction,
		Throwable throwable)
	{
		this(sMessage, iSeverity, sAction, null, null, throwable);
	}
	/**
	 * Constructor for the KOAEvent
	 * 
	 * @param sMessage The message to use in the event
	 * @param iSeverity The severity of the event
	 * @param sAction The action that inits the event
	 * @param sComponent The component that initialized this event.
	 * @param throwable The throwable (exception) for this event. Can be null.
	 * 
	 */
	public KOAEvent(
		String sMessage,
		int iSeverity,
		String sAction,
		String sComponent,
		Throwable throwable)
	{
		this(sMessage, iSeverity, sAction, sComponent, null, throwable);
	}
	/**
	 * Constructor for the KOAEvent
	 * 
	 * @param sMessage The message to use in the event
	 * @param iSeverity The severity of the event
	 * @param sAction The action that inits the event
	 * @param sComponent The component that started the event
	 * @param sActor The actor that initialized this event.
	 * @param throwable The throwable (exception) for this event. Can be null.
	 * 
	 */
	public KOAEvent(
		String sMessage,
		int iSeverity,
		String sAction,
		String sComponent,
		String sActor,
		Throwable throwable)
	{
		/* set the parameters in the super */
		super(sMessage, iSeverity);
		g_sFullMessage = sMessage;
		g_sActor = sActor;
		g_sAction = sAction;
		g_sComponent = sComponent;
		g_tThrowable = throwable;
	}
	/**
	 * Gets the message in this event
	 * 
	 * @return String The message including the stacktrace if provided
	 * 
	 */
	public String getMessage()
	{
		/* return the fullmessage */
		return g_sFullMessage;
	}
	/**
	 * Gets the exception from this event
	 * 
	 * @return Throwable The exception that occures
	 * 
	 */
	public Throwable getException()
	{
		/* return the exception */
		return g_tThrowable;
	}
	/**
	 * Gets the actor that initialized this event.
	 * 
	 * @return String the actor
	 * 
	 */
	public String getActor()
	{
		/* return the actor */
		return g_sActor;
	}
	/**
	 * Gets the component in which this action has started
	 * 
	 * @return String the component
	 * 
	 */
	public String getComponent()
	{
		/* return the actor */
		return g_sComponent;
	}
	/**
	 * Gets the action that has initiated the event.
	 * Can be:
	 * <br>VOTER
	 * <br>DATA_MANAGEMENT
	 * <br>STATE_CHANGE
	 * 
	 * @return String the action that initiates the event
	 * 
	 */
	public String getAction()
	{
		return g_sAction;
	}
}