/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.databeheer.xml.KielijstExportWriter.java
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
import com.logicacmg.koa.constants.TechnicalProps;
import com.logicacmg.koa.exception.KOADataBeheerException;
import com.logicacmg.koa.exception.KOAException;
import com.logicacmg.koa.utils.KOALogHelper;
/**
 * Class for creating a creating a kieslijst export
 */
public class KielijstExportWriter
{
	private Writer xWriter;
	/**
	 * Constructor 
	 * writes an open tag to the writer
	 * 
	 * @param xWriter de xml data wil be writen to this writer
	 */
	public KielijstExportWriter(Writer xWriter) throws KOAException
	{
		try
		{
			this.xWriter = xWriter;
			xWriter.write(
				"<?xml version=\"1.0\" encoding=\""
					+ TechnicalProps.getProperty(
						TechnicalProps.KL_EXPORT_XML_ENCODING)
					+ "\"?>\n");
			xWriter.write(
				"<result action=\"replace\" contenttype=\"kieslijst\">\n");
		}
		catch (IOException ioe)
		{
			String[] params = { "writer" };
			KOALogHelper.logErrorCode(
				"KielijstExportWriter",
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
				"KielijstExportWriter.startMetadata",
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
				"KielijstExportWriter.metadataSubTag",
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
				"KielijstExportWriter.endMetadata",
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
	 * @param sNaam name of the kieskring
	 */
	public void startKiesKring(String sId, String sNaam) throws KOAException
	{
		try
		{
			xWriter.write(
				"\t<kieskring nummer=\""
					+ sId
					+ "\" naam=\""
					+ sNaam
					+ "\">\n");
		}
		catch (IOException ioe)
		{
			String[] params = { "writer" };
			KOALogHelper.logErrorCode(
				"KielijstExportWriter.startKiesKring",
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
				"KielijstExportWriter.endKiesKring",
				ErrorConstants.ERR_IO,
				params,
				ioe);
			throw new KOADataBeheerException(
				KOADataBeheerException.IO_EXCETION,
				ioe);
		}
	}
	/**
	 * writes a district tag with attributes to the writer 
	 * 
	 * @param sId id of the district
	 * @param sNaam name of the district
	 */
	public void district(String sId, String sNaam) throws KOAException
	{
		try
		{
			xWriter.write(
				"\t\t<district nummer=\""
					+ sId
					+ "\" naam=\""
					+ sNaam
					+ "\" />\n");
		}
		catch (IOException ioe)
		{
			String[] params = { "writer" };
			KOALogHelper.logErrorCode(
				"KielijstExportWriter.district",
				ErrorConstants.ERR_IO,
				params,
				ioe);
			throw new KOADataBeheerException(
				KOADataBeheerException.IO_EXCETION,
				ioe);
		}
	}
	/**
	 * writes an open kieslijst tag with attributes to the writer 
	 * 
	 * @param sId id of the district
	 * @param sGroepering name of the goepering
	 */
	public void startKiesLijst(String sId, String sGroepering)
		throws KOAException
	{
		try
		{
			xWriter.write(
				"\t\t<kieslijst nummer=\""
					+ sId
					+ "\" groepering=\""
					+ sGroepering
					+ "\">\n");
		}
		catch (IOException ioe)
		{
			String[] params = { "writer" };
			KOALogHelper.logErrorCode(
				"KielijstExportWriter.startKiesLijst",
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
	public void endKiesLijst() throws KOAException
	{
		try
		{
			xWriter.write("\t\t</kieslijst>\n");
		}
		catch (IOException ioe)
		{
			String[] params = { "writer" };
			KOALogHelper.logErrorCode(
				"KielijstExportWriter.endKiesLijst",
				ErrorConstants.ERR_IO,
				params,
				ioe);
			throw new KOADataBeheerException(
				KOADataBeheerException.IO_EXCETION,
				ioe);
		}
	}
	/**
	 * writes an open positie tag with attributes to the writer 
	 * 
	 * @param sId id of the person on positie
	 * @param sAchternaam achternaam of the person on positie
	 * @param sVoorletters voorletter of the person on positie
	 * @param sRoepnaam roepnaam of the person on positie
	 * @param sGeslacht geslacht of the person on positie
	 * @param sWoonplaats woonplaats of the person on positie
	 */
	public void startPositie(
		String sId,
		String sAchternaam,
		String sVoorletters,
		String sRoepnaam,
		String sGeslacht,
		String sWoonplaats)
		throws KOAException
	{
		try
		{
			xWriter.write(
				"\t\t\t<positie nummer=\""
					+ sId
					+ "\" achternaam=\""
					+ sAchternaam
					+ "\" voorletters=\""
					+ sVoorletters
					+ "\" roepnaam=\""
					+ sRoepnaam
					+ "\" geslacht=\""
					+ sGeslacht
					+ "\" woonplaats=\""
					+ sWoonplaats
					+ "\">\n");
		}
		catch (IOException ioe)
		{
			String[] params = { "writer" };
			KOALogHelper.logErrorCode(
				"KielijstExportWriter.startPositie",
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
	public void endPositie() throws KOAException
	{
		try
		{
			xWriter.write("\t\t\t</positie>\n");
		}
		catch (IOException ioe)
		{
			String[] params = { "writer" };
			KOALogHelper.logErrorCode(
				"KielijstExportWriter.endPositie",
				ErrorConstants.ERR_IO,
				params,
				ioe);
			throw new KOADataBeheerException(
				KOADataBeheerException.IO_EXCETION,
				ioe);
		}
	}
	/**
	 * writes a code tag with value to the writer 
	 * 
	 * @param sCode the value
	 */
	public void code(String sCode) throws KOAException
	{
		try
		{
			xWriter.write("\t\t\t\t<code>" + sCode + "</code>\n");
		}
		catch (IOException ioe)
		{
			String[] params = { "writer" };
			KOALogHelper.logErrorCode(
				"KielijstExportWriter.code",
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
			xWriter.write("</result>");
			xWriter.flush();
			xWriter.close();
		}
		catch (IOException ioe)
		{
			String[] params = { "writer" };
			KOALogHelper.logErrorCode(
				"KielijstExportWriter.close",
				ErrorConstants.ERR_IO,
				params,
				ioe);
			throw new KOADataBeheerException(
				KOADataBeheerException.IO_EXCETION,
				ioe);
		}
	}
}