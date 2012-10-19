// Reversed by Rick using JAD decompiler with some tweaks
// Jad home page: http://www.geocities.com/kpdus/jad.html
// Decompiler options: packimports(3) 
// Source File Name:   FilledInBallot.java

package org.scantegrity.common.ballotstandards.filledInBallot;

import java.io.*;
import java.util.Enumeration;
import java.util.Hashtable;
import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import org.scantegrity.common.ballotstandards.Constants;
import org.scantegrity.common.ballotstandards.SchemaChecker;
import org.scantegrity.common.ballotstandards.basic.Question;
import org.scantegrity.common.ballotstandards.basic.Section;
import org.scantegrity.common.ballotstandards.electionSpecification.ElectionSpecification;
import org.scantegrity.common.ballotstandards.electionSpecification.exceptions.ESException;
import org.scantegrity.common.ballotstandards.filledInBallot.exceptions.FBException;
import org.w3c.dom.Document;
import org.w3c.dom.Node;

public class FilledInBallot
    implements Serializable
{

    /**
	 * 
	 */
	private static final long serialVersionUID = -3292170773263178757L;
	public FilledInBallot()
    {
        id = null;
        sections = null;
        sections = new Hashtable();
    }

    public FilledInBallot(String pathToFile)
        throws FBException
    {
        id = null;
        sections = null;
        DocumentBuilderFactory factory = DocumentBuilderFactory.newInstance();
        Document doc = null;
        try
        {
            doc = factory.newDocumentBuilder().parse(pathToFile);
        }
        catch(Exception e)
        {
            throw new FBException(e);
        }
        buildFilledInBallot(doc.getFirstChild());
    }

    public FilledInBallot(File pathToFile)
        throws FBException
    {
        id = null;
        sections = null;
        DocumentBuilderFactory factory = DocumentBuilderFactory.newInstance();
        Document doc = null;
        try
        {
            doc = factory.newDocumentBuilder().parse(pathToFile);
        }
        catch(Exception e)
        {
            throw new FBException(e);
        }
        buildFilledInBallot(doc.getFirstChild());
    }

    public FilledInBallot(InputStream inputStream)
        throws FBException
    {
        id = null;
        sections = null;
        DocumentBuilderFactory factory = DocumentBuilderFactory.newInstance();
        Document doc = null;
        try
        {
            doc = factory.newDocumentBuilder().parse(inputStream);
        }
        catch(Exception e)
        {
            throw new FBException(e);
        }
        buildFilledInBallot(doc.getFirstChild());
    }

    public FilledInBallot(Node spec)
        throws FBException
    {
        id = null;
        sections = null;
        buildFilledInBallot(spec);
    }
    
    /** TODO: This function was all garbled in the reverse.. probably needs fixing. */

    public boolean checkAgainstSpecification(ElectionSpecification es)
        throws FBException
    {
        Hashtable ess;
        Hashtable fbs;
        String fbsId;
        Enumeration enumS;
        if(getId().compareTo(es.getId()) != 0)
            throw new FBException("The Id of the FilledInBallot does not match the Id of the electionSpecification");
        ess = es.getSections();
        fbs = getSections();
        fbsId = null;
        enumS = fbs.keys();
    	Hashtable fbq = es.getSections();
    	String fbqId;
    	Enumeration enumQ = es.getSections().keys();
    	Hashtable esq = es.getSections();
		while (enumQ.hasMoreElements())
		{
	        String fbaId;
	        fbqId = (String)enumQ.nextElement();
	        if(esq.get(fbqId) == null)
	            throw new FBException((new StringBuilder()).append("The Question with Id |").append(fbsId).append("| from the section with id |").append(fbsId).append("| from the Filled in ballot is not in the Election Specification").toString());
	        Hashtable fba = ((Question)fbq.get(fbqId)).getAnswers();
	        Hashtable esa = ((Question)esq.get(fbqId)).getAnswers();
	        fbaId = null;
	        Enumeration enumA = fba.keys();
	        do
	        {
	            if(!enumA.hasMoreElements())
	                continue; /* Loop/switch isn't completed */
	            fbaId = (String)enumA.nextElement();
	            if(fbaId.startsWith(Constants.WRITEIN))
	                fbaId = Constants.WRITEIN;
	        } while(esa.get(fbaId) != null);
		}
		fbsId = (String)enumS.nextElement();
		if(ess.get(fbsId) == null)
		    throw new FBException((new StringBuilder()).append("The Section with Id |").append(fbsId).append("| from the Filled in ballot is not in the Election Specification").toString());
		fbq = ((Section)fbs.get(fbsId)).getQuestions();
		esq = ((Section)ess.get(fbsId)).getQuestions();
		fbqId = null;
		enumQ = fbq.keys();    
		return true;
    }
    public String getId()
    {
        return id;
    }

    public Hashtable getSections()
    {
        return sections;
    }

    public void setId(String id)
    {
        this.id = id;
    }

    public void setSections(Hashtable sections)
    {
        this.sections = sections;
    }

    public Section[] getOrderedSections()
    {
        int n = sections.size();
        Section ret[] = new Section[n];
        for(Enumeration e = sections.keys(); e.hasMoreElements();)
        {
            Section s = (Section)sections.get(e.nextElement());
            ret[s.getPossition() - 1] = s;
        }

        return ret;
    }

    public Question[] getOrderedQuestions()
    {
        Section sections[] = getOrderedSections();
        int size = 0;
        for(int i = 0; i < sections.length; i++)
            size += sections[i].getQuestions().size();

        Question ret[] = new Question[size];
        int pos = 0;
        for(int i = 0; i < sections.length; i++)
        {
            Section s = sections[i];
            Question qs[] = s.getOrderedQuestions();
            System.arraycopy(qs, 0, ret, pos, qs.length);
            pos += qs.length;
        }

        return ret;
    }

    public String toString()
    {
        return toFortamedString("", "\n");
    }

    public static Document validate(String pathToFile)
        throws ESException
    {
        Document doc = null;
        try
        {
            String pathToSchemaFile = "org/gwu/voting/standardFormat/filledInBallot/FilledInBallot.xsd";
            DocumentBuilderFactory factory = DocumentBuilderFactory.newInstance();
            doc = factory.newDocumentBuilder().parse(pathToFile);
            SchemaChecker schemaChecker = new SchemaChecker(pathToSchemaFile);
            schemaChecker.validate(doc);
        }
        catch(Exception e)
        {
            throw new ESException(e);
        }
        return doc;
    }

    public String toFortamedString(String linePrefix, String lineSufix)
    {
        String s = "";
        s = (new StringBuilder()).append(s).append(linePrefix).append("<?xml version=\"1.0\" encoding=\"ISO-8859-1\" ?>").append(lineSufix).toString();
        s = (new StringBuilder()).append(s).append(linePrefix).append("<").append(Constants.TAG_FILLED_IN_BALLOT).append(" version=\"0.1\">").append(lineSufix).toString();
        s = (new StringBuilder()).append(s).append(linePrefix).append("\t<").append(Constants.TAG_ELECTIONINFO).append(" ").append(Constants.ATTRIBUTE_ID).append("=\"").append(id).append("\">").append(lineSufix).toString();
        s = (new StringBuilder()).append(s).append(linePrefix).append("\t\t<").append(Constants.TAG_SECTIONS).append(">").append(lineSufix).toString();
        for(Enumeration e = sections.elements(); e.hasMoreElements();)
            s = (new StringBuilder()).append(s).append(((Section)e.nextElement()).toFortamedString((new StringBuilder()).append(linePrefix).append("\t\t\t").toString(), lineSufix)).toString();

        s = (new StringBuilder()).append(s).append(linePrefix).append("\t\t</").append(Constants.TAG_SECTIONS).append(">").append(lineSufix).toString();
        s = (new StringBuilder()).append(s).append(linePrefix).append("\t</").append(Constants.TAG_ELECTIONINFO).append(">").append(lineSufix).toString();
        s = (new StringBuilder()).append(s).append(linePrefix).append("</").append(Constants.TAG_FILLED_IN_BALLOT).append(">").append(lineSufix).toString();
        return s;
    }

    private void buildFilledInBallot(Node spec)
        throws FBException
    {
        ElectionSpecification es;
        try
        {
            es = new ElectionSpecification(spec);
        }
        catch(ESException ese)
        {
            throw new FBException(ese);
        }
        id = es.getId();
        sections = es.getSections();
    }

    String id;
    Hashtable sections;
}
