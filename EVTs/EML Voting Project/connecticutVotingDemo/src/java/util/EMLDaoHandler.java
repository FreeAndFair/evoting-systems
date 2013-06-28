package util;
import java.util.HashMap;
import org.xml.sax.Attributes;
import org.xml.sax.SAXException;
import org.xml.sax.helpers.DefaultHandler;


public class EMLDaoHandler extends DefaultHandler {
	
	private HashMap daoObjects = null;
	private StringBuffer buffer = new StringBuffer();
	private String selectionValue = null;
	private String shortCode = null;
	private String candiateId = null;
	private String contestId = null;
	private String globalName=null;
	
	private int flag=0;
	

	//XML PATHS
	private String CONTEST_IDENTIFIER_PATH = "ContestIdentifier";
	private String SELECTION_PATH = "Selection";
	private String CANDIDATEIDENTIFIER_PATH = "CandidateIdentifier";
		
	//XML ATTRIBUTE NAMES
	private String SELECTION_VALUE = "Value";
	private String SHORT_CODE = "Shortcode";
	private String CANDIDATE_ID = "Id";
	private String CONTEST_ID = "Id";
	int i=0;
	
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
		if ((qName!=null)&&(qName.equals(CONTEST_IDENTIFIER_PATH))) {
			contestId=attrs.getValue(CONTEST_ID);
			//globalName=CONTEST_IDENTIFIER_PATH;
		}else if ((qName!=null)&&(qName.equals(SELECTION_PATH))) {
			selectionValue=attrs.getValue(SELECTION_VALUE);
			shortCode = attrs.getValue(SHORT_CODE);	
			System.out.println("Selection value is "+selectionValue);
			daoObjects.put("fID"+contestId+"pID"+shortCode,selectionValue);
			//daoObjects.put(candiateId,selectionValue);
			//daoObjects.put("ballotTransactionID",(String)replaceWild(attrs.getValue(ID)));
		}else if((qName!=null)&&(qName.equals(CANDIDATEIDENTIFIER_PATH))) {
			candiateId=(String)attrs.getValue(CANDIDATE_ID);
			System.out.println("ContestIdentifier Id "+candiateId);
			daoObjects.put("cID"+contestId+"pID"+shortCode,candiateId);	
		}
   }

	public void endElement(String namespaceURI, 
						   String sName, // simple name
						   String qName // qualified name
						   ) throws SAXException {
		if(buffer!=null){
		String text = buffer.toString();	
		System.out.println("CONTEST_IDENTIFIER_PATH in BUF " + buffer.toString());
//		if((candiateId!=null) && (selectionValue!=null)) {
//			daoObjects.put("fID"+contestId+"pID"+shortCode,selectionValue);
//			daoObjects.put(candiateId,selectionValue);
//		}
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

//        if(buf != null)
//        {
//           // buffer.append(buf, offset, len);
//            if(globalName != null)
//                if(globalName.equals(CONTEST_IDENTIFIER_PATH) && buffer != null)
//                {
//                    System.out.println("CONTEST_IDENTIFIER_PATH " + buffer.toString());
//                    daoObjects.put("cID"+contestId, buffer.toString());
//                    globalName = null;
//                } else
//                if(globalName.equals(WRITEIN_CANDIDATE_NAME_PATH) && buffer != null)
//                {
//                    System.out.println("WRITEIN_CANDIDATE_NAME_PATH " + buffer.toString());
//                    daoObjects.put("cID"+contestId+"wID"+shortCode, buffer.toString());
//                    globalName = null;
//                }
//        }
		
	}
	
}