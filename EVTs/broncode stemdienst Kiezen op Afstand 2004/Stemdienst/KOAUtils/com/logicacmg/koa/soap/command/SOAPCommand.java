/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.command.SOAPCommand.java
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
  *  1.0		29-04-2003	XUi 		First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.soap.command;
import com.logica.eplatform.command.TargetableCommand;
import com.logica.eplatform.error.EPlatformException;
import com.logicacmg.koa.soap.request.SOAPRequest;
/**
 * SOAPCommand interface analog to the HTTPCommand
 * but using the SOAPRequest instead of the HTTPRequest
 */
public interface SOAPCommand extends TargetableCommand
{
	/**
	 * Implement this method to initialise the command with the SOAP request
	 * before the command is executed.
	 * 
	 * @param request SOAPRequest to use in the init
	 */
	void init(SOAPRequest request) throws EPlatformException;
}