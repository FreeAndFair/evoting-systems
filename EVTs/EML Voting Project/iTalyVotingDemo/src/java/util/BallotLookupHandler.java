package util;

import java.io.PrintStream;
import java.util.HashMap;
import org.xml.sax.Attributes;
import org.xml.sax.SAXException;
import org.xml.sax.helpers.DefaultHandler;

public class BallotLookupHandler extends DefaultHandler
{

    public BallotLookupHandler()
    {
        daoObjects = null;
        buffer = new StringBuffer();
        checkboxID = null;
        rowID = null;
        qNameGlobal = null;
        flag = 0;
        ID = "ID";
        i = 0;
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
        if(s2 != null && s2.equals(ROW_PATH))
        {
            rowID = attributes.getValue(ID);
            System.out.println("Row ID " + rowID);
            daoObjects.put("rowID" + rowID, rowID);
        } else
        if(s2 != null && s2.equals(CHECKBOX_PATH))
        {
            qNameGlobal = CHECKBOX_PATH;
            checkboxID = attributes.getValue(ID);
            System.out.println("Checkbox ID " + checkboxID);
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
    private String checkboxID;
    private String rowID;
    private String qNameGlobal;
    private int flag;
    private String ID;
    int i;
    private String ROW_PATH;
    private String CHECKBOX_PATH;
}