package util;
import java.util.HashMap;
import org.xml.sax.Attributes;
import org.xml.sax.SAXException;
import org.xml.sax.helpers.DefaultHandler;


public class EMLDaoHandler extends DefaultHandler {
	
	private HashMap daoObjects = null;
	private StringBuffer buffer = new StringBuffer();
	private String selectionValue = null;
	private String candiateId = null;
	
	
	private int flag=0;
	
	//XML ATTRIBUTE NAMES
	private String SELECTION_VALUE = "Value";
	private String CANDIDATE_ID = "Id";
	int i=0;
	
	//XML PATHS
	private String CANDIDATEIDENTIFIER_PATH = "CandidateIdentifier";
	private String SELECTION_PATH = "Selection";
		
	public EMLDaoHandler() {
		this.daoObjects = new HashMap();
	}
	
	//RETURNS PARTIAL LIST VALUES/DATA
	public HashMap getHashMap() {		
		return this.daoObjects;
	}

	public void startElement(String namespaceURI, String lName, // local name
	String qName, // qualified name
	Attributes attrs) throws SAXException {
		buffer = new StringBuffer();
		if ((qName!=null)&&(qName.equals(SELECTION_PATH))) {
			selectionValue=attrs.getValue(SELECTION_VALUE);
			System.out.println("Selection value is "+selectionValue);
			//daoObjects.put("ballotTransactionID",(String)replaceWild(attrs.getValue(ID)));
		}else if((qName!=null)&&(qName.equals(CANDIDATEIDENTIFIER_PATH))) {
			candiateId=(String)attrs.getValue(CANDIDATE_ID);
			System.out.println("ContestIdentifier Id "+candiateId);
			//daoObjects.put("sID"+sideID,sideID);	
		//	i=1;
		}
//		else if(qName.equals(CHECKBOX_PATH)) {	
//			qNameGlobal=CHECKBOX_PATH;
//			checkboxID=(String)replaceWild(attrs.getValue(ID));		   
//			System.out.println("Checkbox ID "+checkboxID);
//			
//			
//			i++;
//		}
   }

	public void endElement(String namespaceURI, 
						   String sName, // simple name
						   String qName // qualified name
						   ) throws SAXException {
		if(buffer!=null){
		String text = buffer.toString();
		if((candiateId!=null) && (selectionValue!=null)) {
			daoObjects.put(candiateId,selectionValue);
		}
		}
//		candiateId=null;
//		selectionValue=null;
	}
	public String replaceWild(String s)
    {
		s= s.replaceAll("\"","");
 		s =s.replaceAll("'","");
		s =s.replaceAll(",","");
		return s;
	}
	public void characters(char buf[], int offset, int len)
		throws SAXException {		
		buffer.append(buf, offset, len);
//		if(qNameGlobal.equals(CHECKBOX_PATH)) {
//		 System.out.println("Buffer "+buffer.toString());
//		 daoObjects.put("sID"+sideID+"cID"+checkboxID,buffer.toString());
//		 qNameGlobal="";
//		}
		
	}
	
}