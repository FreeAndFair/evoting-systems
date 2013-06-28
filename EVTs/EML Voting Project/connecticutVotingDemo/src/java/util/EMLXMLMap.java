package util;

import java.io.ByteArrayInputStream;
import java.util.HashMap;
import javax.xml.parsers.SAXParser;
import javax.xml.parsers.SAXParserFactory;


import org.xml.sax.InputSource;

public class EMLXMLMap {
	private static BallotXMLMap singleton = null;
	//private Hashtable daoObjects = null;    
	private EMLDaoHandler xmlHandler = null;
	
	private SAXParserFactory saxFactory = null;
	private SAXParser saxParser = null;

	public EMLXMLMap() {
		this.saxFactory = SAXParserFactory.newInstance();
		try {
			this.saxParser = saxFactory.newSAXParser();
			this.xmlHandler = new EMLDaoHandler();			
		} catch (Exception e) {
			System.err.println(e.getMessage());
			e.printStackTrace();
		}
	}
	public HashMap getXMLMap(String xmlString) {
		try {
			System.out.println("EML XML Parsing starts...!");
			InputSource xmlSource =
				new InputSource(new ByteArrayInputStream(xmlString.getBytes()));
			this.saxParser.parse(xmlSource, this.xmlHandler);			
		} catch (Exception e) {
			//System.err.println("caught exception in initDaos(): " +  e.getMessage());            
			e.printStackTrace();
		}
		//System.out.println("PLIST SIZE IN XMLPARTLIST "+xmlHandler.getPList().size()); 
		return this.xmlHandler.getHashMap();
	}
}
