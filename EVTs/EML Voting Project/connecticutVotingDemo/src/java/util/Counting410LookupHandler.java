package util;

import java.io.PrintStream;
import java.util.HashMap;
import org.xml.sax.Attributes;
import org.xml.sax.SAXException;
import org.xml.sax.helpers.DefaultHandler;

public class Counting410LookupHandler extends DefaultHandler
{
    private HashMap daoObjects;
    private StringBuffer buffer;
    private String columnID;
    private String officeName;
    private String checkboxID;
    private String partyName; 
    private String candidateName;
    private String displayOrder;
    private String ID;
    private String NAME;
    private String CANDIDATE_NAME;
    private String DISPLAY_ORDER;
    private String qNameGlobal;
    private int flag;  
    int i;
    private String COLUMN_PATH;
    private String CHECKBOX_PATH;

    public Counting410LookupHandler()
    {
    	 
        daoObjects = null;
        buffer = new StringBuffer();
        columnID = null;
        checkboxID = null;
        qNameGlobal = null;
        flag = 0;
        ID = "ID";
        NAME="name";
        i = 0;
        COLUMN_PATH = "column";
        CHECKBOX_PATH = "checkbox";
        CANDIDATE_NAME="CandidateName";
        DISPLAY_ORDER="DisplayOrder";
        daoObjects = new HashMap();
    }

    public HashMap getHashMap()
    {
        return daoObjects;
    }

    public void startElement(String namespaceURI, String lName, String qName, Attributes attrs)
        throws SAXException
    {
        buffer = new StringBuffer();
        if(qName != null && qName.equals(COLUMN_PATH))
        {
            columnID = attrs.getValue(ID);
            officeName=attrs.getValue(NAME);
            System.out.println("OFFICE ID " + columnID+" "+officeName);
            daoObjects.put("fID"+columnID.trim(), officeName);
        } else
        if(qName != null && qName.equals(CHECKBOX_PATH))
        {
            qNameGlobal = CHECKBOX_PATH;
            checkboxID = attrs.getValue(ID);
            partyName = attrs.getValue(NAME);
            candidateName=attrs.getValue(CANDIDATE_NAME);
            displayOrder=attrs.getValue(DISPLAY_ORDER);
            System.out.println("party ID " + checkboxID+" "+partyName+" C NAME "+candidateName);
        }
    }

    public void endElement(String namespaceURI, String lName, String qName)
        throws SAXException
    {
        String text = buffer.toString();
    }

    public String replaceWild(String s)
    {
        s = s.replaceAll("\"", "");
        s = s.replaceAll("'", "");
        s = s.replaceAll(",", "");
        return s;
    }

    public void characters(char ac[], int j, int k)
        throws SAXException
    {
        if(ac != null)
        {
            buffer.append(ac, j, k);
            if(qNameGlobal.equals(CHECKBOX_PATH))
            {
                System.out.println("Buffer " + buffer.toString());
//                if(daoObjects.get(officeID)!=null)
//                	System.out.print("Office Name from Map "+daoObjects.get(officeID));
                daoObjects.put("fID" + columnID + "pID" + checkboxID, buffer.toString());
                daoObjects.put("cID" + columnID + "pID" + checkboxID, candidateName);
                daoObjects.put("dID" + columnID + "pID" + checkboxID, displayOrder);
                daoObjects.put(buffer.toString(),partyName);
                qNameGlobal = "";
            }
        }
    }


}