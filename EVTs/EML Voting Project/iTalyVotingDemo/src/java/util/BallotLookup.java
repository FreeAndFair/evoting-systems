package util;
import java.io.ByteArrayInputStream;
//import java.util.Hashtable;
import java.util.HashMap;
import javax.xml.parsers.SAXParser;
import javax.xml.parsers.SAXParserFactory;

import org.xml.sax.InputSource;

public class BallotLookup {
	private static BallotXMLMap singleton = null;
	//private Hashtable daoObjects = null;    
	private BallotLookupHandler xmlHandler = null;
	
	private SAXParserFactory saxFactory = null;
	private SAXParser saxParser = null;

	public BallotLookup() {
		this.saxFactory = SAXParserFactory.newInstance();
		try {
			this.saxParser = saxFactory.newSAXParser();
			this.xmlHandler = new BallotLookupHandler();			
		} catch (Exception e) {
			System.err.println(e.getMessage());
			e.printStackTrace();
		}
	}

	public HashMap getXMLMap(String xmlString) {
		try {
			InputSource xmlSource =
				new InputSource(new ByteArrayInputStream(xmlString.getBytes()));
			System.out.println("Ballot Lookup parser...!\r\n");
			this.saxParser.parse(xmlSource, this.xmlHandler);
			//ballotVO.setBallotData(this.xmlHandler.getHashMap());
		} catch (Exception e) {
			//System.err.println("caught exception in initDaos(): " +  e.getMessage());            
			e.printStackTrace();
		}
		//System.out.println("PLIST SIZE IN XMLPARTLIST "+xmlHandler.getPList().size()); 
		return this.xmlHandler.getHashMap();
	}
}

