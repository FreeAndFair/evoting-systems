/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.exception.KOADataBeheerException.java
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
import com.logicacmg.koa.exception.KOAException;
/**
 * Exception class for KOA databeheer
 * 
 * @author MRo
 */
public class KOADataBeheerException extends KOAException
{
	public static final String UPLOAD_PARAM_NOT_FOUND = "1000";
	public static final String UPLOAD_EXCEPTION = "1001";
	public static final String STORE_UPLOAD = "1002";
	public static final String UPLOAD_PARSE_XML = "1003";
	public static final String REMOVE_UPLOAD = "1004";
	public static final String PROCESS_KIESLIJST = "1005";
	public static final String EJBEXCEPTION = "1006";
	public static final String KIESKRING_NOT_FOUND = "1007";
	public static final String CREATE_LIJSTPOS_EXCETION = "1008";
	public static final String WRONG_STATE = "1009";
	public static final String WRONG_REPORT = "1010";
	public static final String UPLOAD_SAX_XML = "1011";
	public static final String CREATE_KIESLIJST_EXCETION = "1012";
	public static final String IO_EXCETION = "1013";
	public static final String SQL_EXCETION = "1014";
	/**
	 * Constructor for KOADataBeheerException
	 */
	public KOADataBeheerException()
	{
		super();
	}
	/**
	 * Constructor for KOADataBeheerException
	 * 
		 * @param errorCode			the errorcode associated with this exception
	 */
	public KOADataBeheerException(String errorCode)
	{
		super(errorCode);
	}
	/**
	 * Constructor for KOADataBeheerException
	 * 
		 * @param errorCode			the errorcode associated with this exception
	 * @param params			any additional information
	 */
	public KOADataBeheerException(String errorCode, String[] params)
	{
		super(errorCode, params);
	}
	/**
	 * Constructor for KOADataBeheerException
	 * 
		 * @param errorCode			the errorcode associated with this exception
	 * @param params			any additional information
	 * @param wrappedException	the exception which was the actual reason why this KOADataBeheerException was thrown
	 */
	public KOADataBeheerException(
		String errorCode,
		String[] params,
		Exception wrappedException)
	{
		super(errorCode, params, wrappedException);
	}
	/**
	 * Constructor for KOADataBeheerException
	 * 
		 * @param errorCode			the errorcode associated with this exception
	 * @param params			any additional information
	 * @param wrappedException	the exception which was the actual reason why this KOADataBeheerException was thrown
	 * @param debugMessage		additional string to supply debugging information
	 */
	public KOADataBeheerException(
		String errorCode,
		String[] params,
		Exception wrappedException,
		String debugMessage)
	{
		super(errorCode, params, wrappedException, debugMessage);
	}
	/**
	 * Constructor for KOADataBeheerException
	 * 
		 * @param errorCode			the errorcode associated with this exception
	 * @param wrappedException	the exception which was the actual reason why this KOADataBeheerException was thrown
	 */
	public KOADataBeheerException(String errorCode, Exception wrappedException)
	{
		super(errorCode, wrappedException);
	}
}
