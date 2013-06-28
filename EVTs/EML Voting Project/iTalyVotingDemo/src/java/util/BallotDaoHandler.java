package util;

import java.io.PrintStream;
import java.util.HashMap;
import org.xml.sax.Attributes;
import org.xml.sax.SAXException;
import org.xml.sax.helpers.DefaultHandler;

public class BallotDaoHandler extends DefaultHandler
{

    public BallotDaoHandler()
    {
        daoObjects = null;
        buffer = new StringBuffer();
        transactionID = null;
        checkboxID = null;
        rowID = null;
        qNameGlobal = null;
        flag = 0;
        ID = "ID";
        i = 0;
        BALLOT_PATH = "ballot";
        ROW_PATH = "row";
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
        if(s2 != null && s2.trim().equals(ROW_PATH))
        {
            rowID = attributes.getValue(ID);
            System.out.println("Row ID " + rowID);
            daoObjects.put("rID" + rowID, rowID);
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
                daoObjects.put("rID" + rowID + "cID" + checkboxID, buffer.toString());
                qNameGlobal = "";
            }
        }
    }

    private HashMap daoObjects;
    private StringBuffer buffer;
    private String transactionID;
    private String checkboxID;
    private String rowID;
    private String qNameGlobal;
    private int flag;
    private String ID;
    int i;
    private String BALLOT_PATH;
    private String ROW_PATH;
    private String CHECKBOX_PATH;
}