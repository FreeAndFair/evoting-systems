/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.databeheer.xml.Validator.java
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
  *  1.0		11-04-2003	MRo			First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.databeheer.xml;
import java.util.HashMap;
import java.util.Map;

import org.xml.sax.Attributes;
import org.xml.sax.SAXException;
import org.xml.sax.helpers.DefaultHandler;
/**
 * This class validates a xml file
 * and returns a map with a report of the validation
 */
public class Validator extends DefaultHandler
{
	private String IMPORT = "import";
	public static final String ACTION = "action";
	public static final String CONTENT_TYPE = "contenttype";
	private String META_DATA = "metadata";
	private String KIESKRING = "kieskring";
	private String DISTRICT = "district";
	private String KIESER = "kiezer";
	private String POSITIE = "positie";
	private String KIESLIJST = "kieslijst";
	private int iKieskring = 0;
	private int iDistrict = 0;
	private int iKieser = 0;
	private int iPositie = 0;
	private int iKieslijst = 0;
	private boolean bMetaData;
	private Map xMetaProps = new HashMap();
	private String sTmpQName;
	/**
	 * counts the tags 
	 * and put the tags in the metadata tag in the report map
	 * @see DefaultHandler#startElement(String, String, String, Attributes)
	 */
	public void startElement(
		String sUri,
		String sLocalname,
		String sQName,
		Attributes xAttributes)
		throws SAXException
	{
		if (bMetaData)
		{
			// store the tag name in the sTmpQName for adding to the xMetaProps
			sTmpQName = sQName;
		}
		// count tags	
		else if (sQName.equals(KIESKRING))
		{
			iKieskring++;
		}
		else if (sQName.equals(DISTRICT))
		{
			iDistrict++;
		}
		else if (sQName.equals(KIESER))
		{
			iKieser++;
		}
		else if (sQName.equals(POSITIE))
		{
			iPositie++;
		}
		else if (sQName.equals(KIESLIJST))
		{
			iKieslijst++;
		}
		// if "metadata" tag set metadata flag true for adding data to the xMetaProps
		else if (sQName.equals(META_DATA))
		{
			bMetaData = true;
		}
		// check the "import" tag.
		else if (sQName.equals(IMPORT))
		{
			String sAction = xAttributes.getValue(ACTION);
			String sContentType = xAttributes.getValue(CONTENT_TYPE);
			xMetaProps.put(ACTION, sAction);
			xMetaProps.put(CONTENT_TYPE, sContentType);
		}
	}
	/**
	 * Put the tags in the metadata tag in the report map
	 * @see DefaultHandler#characters(char[], int, int)
	 */
	public void characters(char[] xCharArr, int iStart, int iLength)
		throws SAXException
	{
		if (bMetaData)
		{
			// add tag and CDATA to the xMetaProps
			String sStr = new String(xCharArr, iStart, iLength).trim();
			if (sStr.length() > 0)
			{
				xMetaProps.put(
					sTmpQName,
					new String(xCharArr, iStart, iLength));
			}
		}
	}
	/**
	 * @see DefaultHandler#endElement(String, String, String)
	 */
	public void endElement(String sUri, String sLocalname, String sQName)
		throws SAXException
	{
		if (sQName.equals(META_DATA))
		{
			// end the adding to the xMetaProps
			bMetaData = false;
		}
	}
	/**
	 * put all the counted tag in the report map
	 * @see DefaultHandler#endElement(String, String, String)
	 */
	public void endDocument()
	{
		xMetaProps.put(KIESKRING, (new Integer(iKieskring)).toString());
		xMetaProps.put(DISTRICT, (new Integer(iDistrict)).toString());
		xMetaProps.put(KIESER, (new Integer(iKieser)).toString());
		xMetaProps.put(POSITIE, (new Integer(iPositie)).toString());
		xMetaProps.put(KIESLIJST, (new Integer(iKieslijst)).toString());
	}
	/**
	 * returns the report map
	 * @return Map report map
	 */
	public Map getMetaData()
	{
		return xMetaProps;
	}
}