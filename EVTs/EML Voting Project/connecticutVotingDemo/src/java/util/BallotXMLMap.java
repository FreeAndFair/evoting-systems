package util;

import java.io.ByteArrayInputStream;
import java.util.HashMap;
import javax.xml.parsers.SAXParser;
import javax.xml.parsers.SAXParserFactory;


import org.xml.sax.InputSource;

public class BallotXMLMap {
	private static BallotXMLMap singleton = null;
	//private Hashtable daoObjects = null;    
	private BallotDaoHandler xmlHandler = null;
	
	private SAXParserFactory saxFactory = null;
	private SAXParser saxParser = null;

	public BallotXMLMap() {
		this.saxFactory = SAXParserFactory.newInstance();
		try {
			this.saxParser = saxFactory.newSAXParser();
			this.xmlHandler = new BallotDaoHandler();			
		} catch (Exception e) {
			System.err.println(e.getMessage());
			e.printStackTrace();
		}
	}
	public HashMap getXMLMap(String xmlString) {
		System.out.print("Inside BallotXMLMap class");
		try {
			InputSource xmlSource =
				new InputSource(new ByteArrayInputStream(xmlString.getBytes()));
			this.saxParser.parse(xmlSource, this.xmlHandler);			
		} catch (Exception e) {
			System.err.println("caught exception in initDaos(): " +  e.getMessage());            
			e.printStackTrace();
		}
		//System.out.println("PLIST SIZE IN XMLPARTLIST "+xmlHandler.getPList().size()); 
		return this.xmlHandler.getHashMap();
	}
}
