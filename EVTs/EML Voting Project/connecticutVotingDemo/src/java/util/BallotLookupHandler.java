package util;

import java.io.FileOutputStream;
import java.io.PrintStream;
import java.util.HashMap;
import org.xml.sax.Attributes;
import org.xml.sax.SAXException;
import org.xml.sax.helpers.DefaultHandler;

public class BallotLookupHandler extends DefaultHandler
{
	   private HashMap daoObjects;
	    private StringBuffer buffer;
	    private String checkboxID;
	    private String columnID;
	    private String qNameGlobal;
	    private int flag;
	    private String ID;
	    int i;
	    private String COLUMN_PATH;
	    private String CHECKBOX_PATH;
	    StringBuffer logSB = new StringBuffer(); 

    public BallotLookupHandler()
    {
        daoObjects = null;
        buffer = new StringBuffer();
        checkboxID = null;
        columnID = null;
        qNameGlobal = null;
        flag = 0;
        ID = "ID";
        i = 0;
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
        if(s2 != null && s2.equals(COLUMN_PATH))
        {
            columnID = attributes.getValue(ID);
            logSB.append("Column ID " + columnID);
            writeFile(logSB.toString());
            System.out.println("Column ID " + columnID);
            daoObjects.put("columnID" + columnID, columnID);
        } else
        if(s2 != null && s2.equals(CHECKBOX_PATH))
        {
            qNameGlobal = CHECKBOX_PATH;
            checkboxID = attributes.getValue(ID);
            System.out.println("Checkbox ID " + checkboxID);
            logSB.append("Checkbox ID " + checkboxID);
            writeFile(logSB.toString());
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
            	logSB.append("Buffer " + buffer.toString());
            	writeFile(logSB.toString());
                System.out.println("Buffer " + buffer.toString());
                daoObjects.put("colID" + columnID + "checkID" + checkboxID, buffer.toString());
                qNameGlobal = "";
            }
        }
    }
    public void writeFile(String XMLData)
	 {   
	     try
	     {  
	    	 //FileOutputStream fileoutputstream = new FileOutputStream("counting-ovs.log");
	    	 FileOutputStream fileoutputstream = new FileOutputStream("/home/ovsadmin/public_html/connecticutVotingDemo/ballot_lookup.log");
	         
	         for(int i = 0; i < XMLData.length(); i++)
	             fileoutputstream.write(XMLData.charAt(i));

	         fileoutputstream.close();
	     }
	     catch(Exception exception)
	     {
	         exception.printStackTrace();
	     }
	 }
 
}