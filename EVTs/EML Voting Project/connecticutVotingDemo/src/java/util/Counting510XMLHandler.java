package util;

import java.io.PrintStream;
import java.util.*;
import org.xml.sax.Attributes;
import org.xml.sax.SAXException;
import org.xml.sax.helpers.DefaultHandler;

public class Counting510XMLHandler extends DefaultHandler
{
	    private HashMap daoObjects;
	    private StringBuffer buffer;
	    private String candidateID;
	    private String globalVotes;
	    private List xmlData;
	    private int flag;
	    private String CANDIDATE_ID;
	    int i;
	    private String CANDIDATEIDENTIFIER_PATH;
	    private String VALID_VOTES;

    public Counting510XMLHandler()
    {
        daoObjects = null;
        buffer = new StringBuffer();
        candidateID = null;
        globalVotes = null;
        xmlData = new ArrayList();
        flag = 0;
        CANDIDATE_ID = "ID";
        i = 0;
        CANDIDATEIDENTIFIER_PATH = "CandidateIdentifier";
        VALID_VOTES = "ValidVotes";
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
            candidateID = attributes.getValue(CANDIDATE_ID);
        else
        if(s2 != null && s2.equals(VALID_VOTES))
            globalVotes = VALID_VOTES;
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
            if(globalVotes != null && globalVotes.equals(VALID_VOTES) && buffer != null)
            {
                System.out.println("candidateID " + candidateID + " VALID_VOTES " + buffer.toString());
                daoObjects.put(candidateID, buffer.toString());
                globalVotes = "";
            }
        }
    }

  
}