package util;

import java.io.PrintStream;
import java.util.HashMap;
import org.xml.sax.Attributes;
import org.xml.sax.SAXException;
import org.xml.sax.helpers.DefaultHandler;

public class BallotDaoHandler extends DefaultHandler
{
	  private HashMap daoObjects;
	    private StringBuffer buffer;
	    private String transactionID;
	    private String checkboxID;
	    private String columnID;
	    private String qNameGlobal;
	    private int flag;
	    private String ID;
	    int i;
	    private String BALLOT_PATH;
	    private String COLUMN_PATH;
	    private String CHECKBOX_PATH;
    public BallotDaoHandler()
    {
        daoObjects = null;
        buffer = new StringBuffer();
        transactionID = null;
        checkboxID = null;
        columnID = null;
        qNameGlobal = null;
        flag = 0;
        ID = "ID";
        i = 0;
        BALLOT_PATH = "ballot";
        COLUMN_PATH = "column";
        CHECKBOX_PATH = "checkbox";
        daoObjects = new HashMap();
    }

    public HashMap getHashMap()
    {
        return daoObjects;
    }

    public void startElement(String s, String s1, String s2, Attributes attributes)
        throws SAXException
    {
        buffer = new StringBuffer();
        if(s2 != null && s2.equals(BALLOT_PATH))
        {
            System.out.println("Ballot ID " + attributes.getValue(ID));
            daoObjects.put("ballotTransactionID", attributes.getValue(ID));
        } else
        if(s2 != null && s2.trim().equals(COLUMN_PATH))
        {
            columnID = attributes.getValue(ID);
            System.out.println("Column ID " + columnID);
            daoObjects.put("columnID" + columnID, columnID);
            i = 1;
        } else
        if(s2 != null && s2.equals(CHECKBOX_PATH))
        {
            qNameGlobal = CHECKBOX_PATH;
            checkboxID = attributes.getValue(ID);
            System.out.println("Checkbox ID " + checkboxID);
            i++;
        }
    }

    public void endElement(String s, String s1, String s2)
        throws SAXException
    {
        String s3 = buffer.toString();
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
                daoObjects.put("colID" + columnID + "checkID" + checkboxID, buffer.toString());
                qNameGlobal = "";
            }
        }
    }

  
}