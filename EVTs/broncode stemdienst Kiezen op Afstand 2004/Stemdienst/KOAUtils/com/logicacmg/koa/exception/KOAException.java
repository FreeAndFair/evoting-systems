/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.exception.KOAException.java
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
  *  0.1		15-04-2003	MRo			First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.exception;

import com.logica.eplatform.error.EPlatformException;

/**
 * Exception class for KOA
 * 
 * @author MRo
 */
public class KOAException extends EPlatformException
{
	/**
	 * Constructor for KOAException.
	 */
	public KOAException()
	{
		super();
	}
	/**
	 * Constructor for KOAException
	 * 
	 * @param errorCode 	the errorcode associated with this exception
	 */
	public KOAException(String errorCode)
	{
		super(errorCode);
	}
	/**
	 * Constructor for KOAException
	 * 
	 * @param errorCode		the errorcode associated with this exception
	 * @param params		any additional information
	 */
	public KOAException(String errorCode, String[] params)
	{
		super(errorCode, params);
	}
	/**
	 * Constructor for KOAException
	 * 
		 * @param errorCode			the errorcode associated with this exception
	 * @param params			any additional information
	 * @param wrappedException	the exception which was the actual reason why this KOAException was thrown
	 */
	public KOAException(
		String errorCode,
		String[] params,
		Exception wrappedException)
	{
		super(errorCode, params, wrappedException);
	}
	/**
	 * Constructor for KOAException
	 * 
		 * @param errorCode			the errorcode associated with this exception
	 * @param params			any additional information
	 * @param wrappedException	the exception which was the actual reason why this KOAException was thrown
	 * @param debugMessage		additional string to supply debugging information
	 */
	public KOAException(
		String errorCode,
		String[] params,
		Exception wrappedException,
		String debugMessage)
	{
		super(errorCode, params, wrappedException, debugMessage);
	}
	/**
	 * Constructor for KOAException
	 * 
		 * @param errorCode			the errorcode associated with this exception
	 * @param wrappedException	the exception which was the actual reason why this KOAException was thrown
	 */
	public KOAException(String errorCode, Exception wrappedException)
	{
		super(errorCode, wrappedException);
	}
}