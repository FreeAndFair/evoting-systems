/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.databeheer.xml.KiesRegisterExportWriter.java
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
  *  0.1		14-04-2003	MRo			First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.databeheer.xml;
import java.io.IOException;
import java.io.Writer;

import com.logicacmg.koa.constants.ErrorConstants;
import com.logicacmg.koa.exception.KOADataBeheerException;
import com.logicacmg.koa.exception.KOAException;
import com.logicacmg.koa.utils.KOALogHelper;
/**
 * Class for creating a creating a KiesRegister export
 */
public class KiesRegisterExportWriter
{
	private Writer xWriter;
	/**
	 * Constructor 
	 * writes an open tag to the writer
	 * 
	 * @param xWriter de xml data wil be writen to this writer
	 */
	public KiesRegisterExportWriter(Writer xWriter, String action)
		throws KOAException
	{
		String sAction = action;
		try
		{
			this.xWriter = xWriter;
			xWriter.write("<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n");
			xWriter.write(
				"<result action=\""
					+ sAction
					+ "\" contenttype=\"kiezersregister\">\n");
		}
		catch (IOException ioe)
		{
			String[] params = { "writer" };
			KOALogHelper.logErrorCode(
				"KiesRegisterExportWriter",
				ErrorConstants.ERR_IO,
				params,
				ioe);
			throw new KOADataBeheerException(
				KOADataBeheerException.IO_EXCETION,
				ioe);
		}
	}
	/**
	 * writes an open metatdata tag to the writer
	 */
	public void startMetadata() throws KOAException
	{
		try
		{
			xWriter.write("\t<metadata>\n");
		}
		catch (IOException ioe)
		{
			String[] params = { "writer" };
			KOALogHelper.logErrorCode(
				"KiesRegisterExportWriter.startMetadata",
				ErrorConstants.ERR_IO,
				params,
				ioe);
			throw new KOADataBeheerException(
				KOADataBeheerException.IO_EXCETION,
				ioe);
		}
	}
	/**
	 * writes an tag in metatdata writer
	 * 
	 * @param sTagName the name of the tag
	 * @param sValue the value of the tag
	 */
	public void metadataSubTag(String sTagName, String sValue)
		throws KOAException
	{
		try
		{
			xWriter.write(
				"\t\t<" + sTagName + ">" + sValue + "</" + sTagName + ">\n");
		}
		catch (IOException ioe)
		{
			String[] params = { "writer" };
			KOALogHelper.logErrorCode(
				"KiesRegisterExportWriter.metadataSubTag",
				ErrorConstants.ERR_IO,
				params,
				ioe);
			throw new KOADataBeheerException(
				KOADataBeheerException.IO_EXCETION,
				ioe);
		}
	}
	/**
	 * writes an close metatdata tag to the writer
	 */
	public void endMetadata() throws KOAException
	{
		try
		{
			xWriter.write("\t</metadata>\n");
		}
		catch (IOException ioe)
		{
			String[] params = { "writer" };
			KOALogHelper.logErrorCode(
				"KiesRegisterExportWriter.endMetadata",
				ErrorConstants.ERR_IO,
				params,
				ioe);
			throw new KOADataBeheerException(
				KOADataBeheerException.IO_EXCETION,
				ioe);
		}
	}
	/**
	 * writes an open kieskring tag with attributes to the writer 
	 * 
	 * @param sId id of the kieskring
	 */
	public void startKiesKring(String sId) throws KOAException
	{
		try
		{
			xWriter.write("\t<kieskring nummer=\"" + sId + "\">\n");
		}
		catch (IOException ioe)
		{
			String[] params = { "writer" };
			KOALogHelper.logErrorCode(
				"KiesRegisterExportWriter.startKiesKring",
				ErrorConstants.ERR_IO,
				params,
				ioe);
			throw new KOADataBeheerException(
				KOADataBeheerException.IO_EXCETION,
				ioe);
		}
	}
	/**
	 * writes an close kieskring tag to the writer
	 */
	public void endKiesKring() throws KOAException
	{
		try
		{
			xWriter.write("\t</kieskring>\n");
		}
		catch (IOException ioe)
		{
			String[] params = { "writer" };
			KOALogHelper.logErrorCode(
				"KiesRegisterExportWriter.endKiesKring",
				ErrorConstants.ERR_IO,
				params,
				ioe);
			throw new KOADataBeheerException(
				KOADataBeheerException.IO_EXCETION,
				ioe);
		}
	}
	/**
	 * writes a open district tag with attributes to the writer 
	 * 
	 * @param sId id of the district
	 */
	public void startDistrict(String sId) throws KOAException
	{
		try
		{
			xWriter.write("\t\t<district nummer=\"" + sId + "\">\n");
		}
		catch (IOException ioe)
		{
			String[] params = { "writer" };
			KOALogHelper.logErrorCode(
				"KiesRegisterExportWriter.startDistrict",
				ErrorConstants.ERR_IO,
				params,
				ioe);
			throw new KOADataBeheerException(
				KOADataBeheerException.IO_EXCETION,
				ioe);
		}
	}
	/**
	 * writes an close district tag to the writer
	 */
	public void endDistrict() throws KOAException
	{
		try
		{
			xWriter.write("\t\t</district>\n");
		}
		catch (IOException ioe)
		{
			String[] params = { "writer" };
			KOALogHelper.logErrorCode(
				"KiesRegisterExportWriter.endDistrict",
				ErrorConstants.ERR_IO,
				params,
				ioe);
			throw new KOADataBeheerException(
				KOADataBeheerException.IO_EXCETION,
				ioe);
		}
	}
	/**
	 * writes a kiezer tag with attributes and a hashedww tag to the writer 
	 * 
	 * @param sId id of the kiezer
	 * @param sHashedWW hashed passwoord of the kiezer
	 * @param sStemcode stemcode of the kiezer
	 */
	public void kiezer(String sId, String sHashedWW, String sStemcode)
		throws KOAException
	{
		try
		{
			xWriter.write("\t\t\t<kiezer id=\"" + sId + "\">\n");
			xWriter.write("\t\t\t\t<stemcode>" + sStemcode + "</stemcode>\n");
			xWriter.write(
				"\t\t\t\t<hashedww><![CDATA[" + sHashedWW + "]]></hashedww>\n");
			xWriter.write("\t\t\t</kiezer>\n");
		}
		catch (IOException ioe)
		{
			String[] params = { "writer" };
			KOALogHelper.logErrorCode(
				"KiesRegisterExportWriter.kiezer",
				ErrorConstants.ERR_IO,
				params,
				ioe);
			throw new KOADataBeheerException(
				KOADataBeheerException.IO_EXCETION,
				ioe);
		}
	}
	/**
	 * writes a close tag to the writer 
	 * and closes the writer.
	 * 
	 */
	public void close() throws KOAException
	{
		try
		{
			xWriter.write("</result>\n");
			xWriter.close();
		}
		catch (IOException ioe)
		{
			String[] params = { "writer" };
			KOALogHelper.logErrorCode(
				"KiesRegisterExportWriter.close",
				ErrorConstants.ERR_IO,
				params,
				ioe);
			throw new KOADataBeheerException(
				KOADataBeheerException.IO_EXCETION,
				ioe);
		}
	}
}