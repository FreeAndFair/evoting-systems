/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.databeheer.xml.WrongIdWriter.java
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
  *  0.1		14-04-2003	MRo		First implementation
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
 * Class for creating a creating a wrong id's list export
 */
public class WrongIdWriter
{
	public static final String NOT_FOUND = "notFound";
	public static final String DUBLICATE = "dublicate";
	public static final String IS_REMOVED = "isAlreadyRemoved";
	public static final String HAS_VOTED = "hasVoted";
	public static final String UNKNOWN_KIEZER = "UnknownKiezer";
	public static final String NOT_FOUND_KIESKRING = "parentnotFound";
	private Writer xWriter;
	/**
	 * Constructor 
	 * writes an open tag to the writer
	 * 
	 * @param xWriter de xml data wil be writen to this writer
	 */
	public WrongIdWriter(Writer xWriter) throws KOAException
	{
		try
		{
			this.xWriter = xWriter;
			xWriter.write("<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n");
			xWriter.write("<wrongids>\n");
		}
		catch (IOException ioe)
		{
			String[] params = { "writer" };
			KOALogHelper.logErrorCode(
				"WrongIdWriter",
				ErrorConstants.ERR_IO,
				params,
				ioe);
			throw new KOADataBeheerException(
				KOADataBeheerException.IO_EXCETION,
				ioe);
		}
	}
	/**
	 * writes an kieskring tag with attributes to the writer 
	 * 
	 * @param kieskringId id of kieskring
	 * @param reason reason of adding to this xml
	 */
	public void writeKiesKring(String kieskringId, String reason)
		throws KOAException
	{
		try
		{
			xWriter.write(
				"\t<kieskring kieskringid =\""
					+ kieskringId
					+ "\" reason=\""
					+ reason
					+ "\" />\n");
		}
		catch (IOException ioe)
		{
			String[] params = { "writer" };
			KOALogHelper.logErrorCode(
				"WrongIdWriter.writeKiesKring",
				ErrorConstants.ERR_IO,
				params,
				ioe);
			throw new KOADataBeheerException(
				KOADataBeheerException.IO_EXCETION,
				ioe);
		}
	}
	/**
	 * writes an kieslijst tag with attributes to the writer 
	 * 
	 * @param kieslijstId id of kieslijst
	 * @param kieskringId id of kieskring
	 * @param reason reason of adding to this xml
	 */
	public void writeKiesLijst(
		String kieslijstId,
		String kieskringId,
		String reason)
		throws KOAException
	{
		try
		{
			xWriter.write(
				"\t<kieslijst kieslijstid=\""
					+ kieslijstId
					+ "\" kieskringid=\""
					+ kieskringId
					+ "\" reason=\""
					+ reason
					+ "\" />\n");
		}
		catch (IOException ioe)
		{
			String[] params = { "writer" };
			KOALogHelper.logErrorCode(
				"WrongIdWriter.writeKiesLijst",
				ErrorConstants.ERR_IO,
				params,
				ioe);
			throw new KOADataBeheerException(
				KOADataBeheerException.IO_EXCETION,
				ioe);
		}
	}
	/**
	 * writes an positie tag with attributes to the writer 
	 * 
	 * @param lijstPosId id of posistie
	 * @param kieslijstId id of kieslijst
	 * @param kieskringId id of kieskring
	 * @param reason reason of adding to this xml
	 */
	public void writePositie(
		String lijstPosId,
		String kieslijstId,
		String kieskringId,
		String reason)
		throws KOAException
	{
		try
		{
			xWriter.write(
				"\t<positie lijstpositieid=\""
					+ lijstPosId
					+ "\" kieslijstid=\""
					+ kieslijstId
					+ "\" kieskringid=\""
					+ kieskringId
					+ "\" reason=\""
					+ reason
					+ "\" />\n");
		}
		catch (IOException ioe)
		{
			String[] params = { "writer" };
			KOALogHelper.logErrorCode(
				"WrongIdWriter.writePositie",
				ErrorConstants.ERR_IO,
				params,
				ioe);
			throw new KOADataBeheerException(
				KOADataBeheerException.IO_EXCETION,
				ioe);
		}
	}
	/**
	 * writes an kiezer tag with attributes to the writer 
	 * 
	 * @param kiezerId id of kiezer
	 * @param districtId id of district
	 * @param kieskringId id of kieskring
	 * @param reason reason of adding to this xml
	 */
	public void writeKiezer(
		String kiezerId,
		String districtId,
		String kieskringId,
		String reason)
		throws KOAException
	{
		try
		{
			xWriter.write(
				"\t<kiezer kiezerid=\""
					+ kiezerId
					+ "\" districtid=\""
					+ districtId
					+ "\" kieskringid=\""
					+ kieskringId
					+ "\" reason=\""
					+ reason
					+ "\" />\n");
		}
		catch (IOException ioe)
		{
			String[] params = { "writer" };
			KOALogHelper.logErrorCode(
				"WrongIdWriter.writeKiezer",
				ErrorConstants.ERR_IO,
				params,
				ioe);
			throw new KOADataBeheerException(
				KOADataBeheerException.IO_EXCETION,
				ioe);
		}
	}
	/**
	 * writes an kiezer tag with attributes to the writer 
	 * 
	 * @param kiezerId id of kiezer
	 * @param reason reason of adding to this xml
	 */
	public void writeKiezer(String kiezerId, String reason) throws KOAException
	{
		try
		{
			xWriter.write(
				"\t<kiezer kiezerid=\""
					+ kiezerId
					+ "\" reason=\""
					+ reason
					+ "\" />\n");
		}
		catch (IOException ioe)
		{
			String[] params = { "writer" };
			KOALogHelper.logErrorCode(
				"WrongIdWriter.writeKiezer",
				ErrorConstants.ERR_IO,
				params,
				ioe);
			throw new KOADataBeheerException(
				KOADataBeheerException.IO_EXCETION,
				ioe);
		}
	}
	/**
	 * writes an district tag with attributes to the writer 
	 * 
	 * @param districtId id of district
	 * @param kieskringId id of kieskring
	 * @param reason reason of adding to this xml
	 */
	public void writeDistrict(
		String districtId,
		String kieskringId,
		String reason)
		throws KOAException
	{
		try
		{
			xWriter.write(
				"\t<district districtid=\""
					+ districtId
					+ "\" kieskringid=\""
					+ kieskringId
					+ "\" reason=\""
					+ reason
					+ "\" />\n");
		}
		catch (IOException ioe)
		{
			String[] params = { "writer" };
			KOALogHelper.logErrorCode(
				"WrongIdWriter.writeDistrict",
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
			xWriter.write("</wrongids>\n");
			xWriter.close();
		}
		catch (IOException ioe)
		{
			String[] params = { "writer" };
			KOALogHelper.logErrorCode(
				"WrongIdWriter.close",
				ErrorConstants.ERR_IO,
				params,
				ioe);
			throw new KOADataBeheerException(
				KOADataBeheerException.IO_EXCETION,
				ioe);
		}
	}
}