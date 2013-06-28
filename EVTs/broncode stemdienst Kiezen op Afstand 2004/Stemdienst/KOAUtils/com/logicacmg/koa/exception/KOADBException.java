/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.exception.KOADBException.java
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
  *  0.1		16-04-2003	MKu			First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.exception;
import com.logicacmg.koa.exception.KOAException;
/**
 * Exception class for errors concerning db issues for KOA
 * 
 * @author KuijerM
 */
public class KOADBException extends KOAException
{
	/**
	 * Constructor for KOADBException
	 */
	public KOADBException()
	{
		super();
	}
	/**
	 * Constructor for KOADBException
	 * 
		 * @param errorCode			the errorcode associated with this exception
	 */
	public KOADBException(String errorCode)
	{
		super(errorCode);
	}
	/**
	 * Constructor for KOADBException
	 * 
		 * @param errorCode			the errorcode associated with this exception
	 * @param params			any additional information
	 */
	public KOADBException(String errorCode, String[] params)
	{
		super(errorCode, params);
	}
	/**
	 * Constructor for KOADBException
	 * 
		 * @param errorCode			the errorcode associated with this exception
	 * @param params			any additional information
	 * @param wrappedException	the exception which was the actual reason why this KOADBException was thrown
	 */
	public KOADBException(
		String errorCode,
		String[] params,
		Exception wrappedException)
	{
		super(errorCode, params, wrappedException);
	}
	/**
	 * Constructor for KOADBException
	 * 
		 * @param errorCode			the errorcode associated with this exception
	 * @param params			any additional information
	 * @param wrappedException	the exception which was the actual reason why this KOADBException was thrown
	 * @param debugMessage		additional string to supply debugging information
	 */
	public KOADBException(
		String errorCode,
		String[] params,
		Exception wrappedException,
		String debugMessage)
	{
		super(errorCode, params, wrappedException, debugMessage);
	}
	/**
	 * Constructor for KOADBException
	 * 
		 * @param errorCode			the errorcode associated with this exception
	 * @param wrappedException	the exception which was the actual reason why this KOADBException was thrown
	 */
	public KOADBException(String errorCode, Exception wrappedException)
	{
		super(errorCode, wrappedException);
	}
}