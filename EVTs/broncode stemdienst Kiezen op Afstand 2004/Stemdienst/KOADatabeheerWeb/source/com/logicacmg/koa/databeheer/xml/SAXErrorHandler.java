/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.databeheer.xml.SAXErrorHandler.java
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
  *  1.0		14-04-2003	MRo		First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.databeheer.xml;
import org.xml.sax.ErrorHandler;
import org.xml.sax.SAXException;
import org.xml.sax.SAXParseException;
/**
 * Error handler for a sax parser
 */
public class SAXErrorHandler implements ErrorHandler
{
	/**
	 * @see ErrorHandler#error(SAXParseException)
	 * 
	 * throws the exception if there is an error
	 */
	public void error(SAXParseException spe) throws SAXException
	{
		throw spe;
	}
	/**
	 * @see ErrorHandler#fatalError(SAXParseException)
	 * 
	 * throws the exception if there is a fatal error
	 */
	public void fatalError(SAXParseException spe) throws SAXException
	{
		throw spe;
	}
	/**
	 * @see ErrorHandler#warning(SAXParseException)
	 * 
	 * throws the exception if there is a fatal warning
	 */
	public void warning(SAXParseException spe) throws SAXException
	{
		throw spe;
	}
}
