package util;

import java.io.PrintStream;
import java.util.*;
import org.xml.sax.Attributes;
import org.xml.sax.SAXException;
import org.xml.sax.helpers.DefaultHandler;

public class Counting410LookupHandler extends DefaultHandler
{

    public Counting410LookupHandler()
    {
        daoObjects = null;
        buffer = new StringBuffer();
        candidateID = null;
        globalName = null;
        xmlData = new ArrayList();
        flag = 0;
        CANDIDATE_ID = "Id";
        i = 0;
        CANDIDATEIDENTIFIER_PATH = "CandidateIdentifier";
        CANDIDATE_NAME = "CandidateName";
        REGISTERED_NAME = "RegisteredName";
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
        if(s2 != null && s2.equals(CANDIDATEIDENTIFIER_PATH))
        {
            candidateID = attributes.getValue(CANDIDATE_ID);
            System.out.println("candidateID " + candidateID);
        } else
        if(s2 != null && s2.equals(CANDIDATE_NAME))
            globalName = CANDIDATE_NAME;
        else
        if(s2 != null && s2.equals(REGISTERED_NAME))
            globalName = REGISTERED_NAME;
    }

    public void endElement(String s, String s1, String s2)
        throws SAXException
    {
        String s3;
        if(buffer != null)
            s3 = buffer.toString();
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
            if(globalName != null)
                if(globalName.equals(CANDIDATE_NAME) && buffer != null)
                {
                    System.out.println("CANDIDATE_NAME " + buffer.toString());
                    daoObjects.put(candidateID + CANDIDATE_NAME, buffer.toString());
                    globalName = "";
                } else
                if(globalName.equals(REGISTERED_NAME) && buffer != null)
                {
                    System.out.println("REGISTERED_NAME " + buffer.toString());
                    daoObjects.put(candidateID + REGISTERED_NAME, buffer.toString());
                    globalName = "";
                }
        }
    }

    private HashMap daoObjects;
    private StringBuffer buffer;
    private String candidateID;
    private String globalName;
    private List xmlData;
    private int flag;
    private String CANDIDATE_ID;
    int i;
    private String CANDIDATEIDENTIFIER_PATH;
    private String CANDIDATE_NAME;
    private String REGISTERED_NAME;
}