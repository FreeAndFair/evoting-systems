// Reversed by Rick using JAD decompiler with some tweaks
// Jad home page: http://www.geocities.com/kpdus/jad.html
// Decompiler options: packimports(3) 
// Source File Name:   Results.java

package org.scantegrity.common.ballotstandards.results;

import java.io.*;
import java.util.Enumeration;
import java.util.Hashtable;
import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import org.scantegrity.common.ballotstandards.Constants;
import org.scantegrity.common.ballotstandards.SchemaChecker;
import org.scantegrity.common.ballotstandards.basic.*;
import org.scantegrity.common.ballotstandards.electionSpecification.ElectionSpecification;
import org.scantegrity.common.ballotstandards.electionSpecification.exceptions.ESException;
import org.scantegrity.common.ballotstandards.results.exceptions.RException;
import org.w3c.dom.Document;
import org.w3c.dom.Node;

public class Results
    implements Serializable
{

    /**
	 * 
	 */
	private static final long serialVersionUID = -6088058855806403689L;
	public Results()
    {
    }

    public Results(String pathToFile)
        throws RException
    {
        DocumentBuilderFactory factory = DocumentBuilderFactory.newInstance();
        Document doc = null;
        try
        {
            doc = factory.newDocumentBuilder().parse(pathToFile);
        }
        catch(Exception e)
        {
            throw new RException(e);
        }
        buildResults(doc.getFirstChild());
    }

    public Results(File pathToFile)
        throws RException
    {
        DocumentBuilderFactory factory = DocumentBuilderFactory.newInstance();
        Document doc = null;
        try
        {
            doc = factory.newDocumentBuilder().parse(pathToFile);
        }
        catch(Exception e)
        {
            throw new RException(e);
        }
        buildResults(doc.getFirstChild());
    }

    public Results(InputStream inputStream)
        throws RException
    {
        DocumentBuilderFactory factory = DocumentBuilderFactory.newInstance();
        Document doc = null;
        try
        {
            doc = factory.newDocumentBuilder().parse(inputStream);
        }
        catch(Exception e)
        {
            throw new RException(e);
        }
        buildResults(doc.getFirstChild());
    }

    public Results(Node spec)
        throws RException
    {
        buildResults(spec);
    }

    /** TODO: Mangled during the reverse, will need to be fixed. **/
    
    public boolean checkAgainstSpecification(ElectionSpecification es)
        throws RException
    {
    	/*
        Hashtable ess;
        Hashtable fbs;
        String fbsId;
        Enumeration enumS;
        if(getId().compareTo(es.getId()) != 0)
            throw new RException("The Id of the FilledInBallot does not match the Id of the electionSpecification");
        ess = es.getSections();
        fbs = getSections();
        fbsId = null;
        enumS = fbs.keys();
_L2:
        Hashtable fbq;
        Hashtable esq;
        String fbqId;
        Enumeration enumQ;
        if(!enumS.hasMoreElements())
            break MISSING_BLOCK_LABEL_362;
        fbsId = (String)enumS.nextElement();
        if(ess.get(fbsId) == null)
            throw new RException((new StringBuilder()).append("The Section with Id |").append(fbsId).append("| from the Filled in ballot is not in the Election Specification").toString());
        fbq = ((Section)fbs.get(fbsId)).getQuestions();
        esq = ((Section)ess.get(fbsId)).getQuestions();
        fbqId = null;
        enumQ = fbq.keys();
_L4:
        if(!enumQ.hasMoreElements()) goto _L2; else goto _L1
_L1:
        String fbaId;
        fbqId = (String)enumQ.nextElement();
        if(esq.get(fbqId) == null)
            throw new RException((new StringBuilder()).append("The Question with Id |").append(fbsId).append("| from the section with id |").append(fbsId).append("| from the Filled in ballot is not in the Election Specification").toString());
        Hashtable fba = ((Question)fbq.get(fbqId)).getAnswers();
        Hashtable esa = ((Question)esq.get(fbqId)).getAnswers();
        fbaId = null;
        Enumeration enumA = fba.keys();
        do
        {
            if(!enumA.hasMoreElements())
                continue; /* Loop/switch isn't completed 
            fbaId = (String)enumA.nextElement();
        } while(fbaId.startsWith(Constants.WRITEIN) || esa.get(fbaId) != null);
        break; /* Loop/switch isn't completed 
        if(true) goto _L4; else goto _L3
_L3:
        throw new RException((new StringBuilder()).append("The Answer with Id |").append(fbaId).append("|from Question with Id |").append(fbqId).append("| from the section with id |").append(fbsId).append("| from the Filled in ballot is not in the Election Specification").toString());
        */
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
            String pathToSchemaFile = "org/gwu/voting/standardFormat/results/Results.xsd";
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
        s = (new StringBuilder()).append(s).append(linePrefix).append("<").append(Constants.TAG_RESULTS).append(" version=\"0.1\">").append(lineSufix).toString();
        s = (new StringBuilder()).append(s).append(linePrefix).append("\t<").append(Constants.TAG_ELECTIONINFO).append(" ").append(Constants.ATTRIBUTE_ID).append("=\"").append(id).append("\">").append(lineSufix).toString();
        s = (new StringBuilder()).append(s).append(linePrefix).append("\t\t<").append(Constants.TAG_SECTIONS).append(">").append(lineSufix).toString();
        for(Enumeration e = sections.elements(); e.hasMoreElements();)
            s = (new StringBuilder()).append(s).append(((Section)e.nextElement()).toFortamedString((new StringBuilder()).append(linePrefix).append("\t\t\t").toString(), lineSufix)).toString();

        s = (new StringBuilder()).append(s).append(linePrefix).append("\t\t</").append(Constants.TAG_SECTIONS).append(">").append(lineSufix).toString();
        s = (new StringBuilder()).append(s).append(linePrefix).append("\t</").append(Constants.TAG_ELECTIONINFO).append(">").append(lineSufix).toString();
        s = (new StringBuilder()).append(s).append(linePrefix).append("</").append(Constants.TAG_RESULTS).append(">").append(lineSufix).toString();
        return s;
    }

    /** TODO: Mangled during reverse, will need to be fixed. **/
    public boolean equals(Results results)
    {
    	/*
        Enumeration s;
        Hashtable thisSections = getSections();
        if(thisSections.size() != results.getSections().size())
            return false;
        s = thisSections.elements();
_L2:
        Section resultsSection;
        Enumeration q;
        if(!s.hasMoreElements())
            break MISSING_BLOCK_LABEL_253;
        Section thisSection = (Section)s.nextElement();
        resultsSection = (Section)results.getSections().get(thisSection.getId());
        if(resultsSection == null)
            return false;
        Hashtable thisQuestions = thisSection.getQuestions();
        if(thisQuestions.size() != resultsSection.getQuestions().size())
            return false;
        q = thisQuestions.elements();
_L4:
        if(!q.hasMoreElements()) goto _L2; else goto _L1
_L1:
        Question thisQuestion = (Question)q.nextElement();
        Question resultsQuestion = (Question)resultsSection.getQuestions().get(thisQuestion.getId());
        if(resultsQuestion == null)
            return false;
        Hashtable answers = thisQuestion.getAnswers();
        if(answers.size() != resultsQuestion.getAnswers().size())
            return false;
        Enumeration a = answers.elements();
        Answer thisAnswer;
        Answer resultsAnswer;
        do
        {
            if(!a.hasMoreElements())
                continue; /* Loop/switch isn't completed 
            thisAnswer = (Answer)a.nextElement();
            resultsAnswer = (Answer)resultsQuestion.getAnswers().get(thisAnswer.getId());
            if(resultsAnswer == null)
                return false;
        } while(thisAnswer.getPoints() == resultsAnswer.getPoints());
        break; /* Loop/switch isn't completed 
        if(true) goto _L4; else goto _L3
_L3:
        return false;
        */
        return true;
    }

    private void buildResults(Node spec)
        throws RException
    {
        ElectionSpecification es;
        try
        {
            es = new ElectionSpecification(spec);
        }
        catch(ESException ese)
        {
            throw new RException(ese);
        }
        id = es.getId();
        sections = es.getSections();
    }

    String id;
    Hashtable sections;
}
