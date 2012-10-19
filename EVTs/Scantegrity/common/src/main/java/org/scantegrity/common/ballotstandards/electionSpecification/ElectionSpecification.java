// Reversed by Rick using JAD decompiler with some tweaks
// Jad home page: http://www.geocities.com/kpdus/jad.html
// Decompiler options: packimports(3) 
// Source File Name:   ElectionSpecification.java

package org.scantegrity.common.ballotstandards.electionSpecification;

import java.io.*;
import java.util.Enumeration;
import java.util.Hashtable;
import javax.xml.parsers.DocumentBuilderFactory;
import org.scantegrity.common.ballotstandards.Constants;
import org.scantegrity.common.ballotstandards.SchemaChecker;
import org.scantegrity.common.ballotstandards.basic.Question;
import org.scantegrity.common.ballotstandards.basic.Section;
import org.scantegrity.common.ballotstandards.basic.exceptions.BasicException;
import org.scantegrity.common.ballotstandards.electionSpecification.exceptions.ESException;
import org.w3c.dom.*;

public class ElectionSpecification
    implements Serializable
{

    /**
	 * 
	 */
	private static final long serialVersionUID = 8030167179571795413L;
	public ElectionSpecification()
    {
    }

    public ElectionSpecification(String id, Hashtable<String, Section> s)
    {
        this.id = id;
        sections = s;
    }

    public ElectionSpecification(String pathToFile)
        throws ESException
    {
        DocumentBuilderFactory factory = DocumentBuilderFactory.newInstance();
        Document doc = null;
        try
        {
            doc = factory.newDocumentBuilder().parse(pathToFile);
        }
        catch(Exception e)
        {
            throw new ESException(e);
        }
        buildElectionSpecification(doc.getFirstChild());
    }

    public ElectionSpecification(File pathToFile)
        throws ESException
    {
        DocumentBuilderFactory factory = DocumentBuilderFactory.newInstance();
        Document doc = null;
        try
        {
            doc = factory.newDocumentBuilder().parse(pathToFile);
        }
        catch(Exception e)
        {
            throw new ESException(e);
        }
        buildElectionSpecification(doc.getFirstChild());
    }

    public ElectionSpecification(InputStream inputStream)
        throws ESException
    {
        DocumentBuilderFactory factory = DocumentBuilderFactory.newInstance();
        Document doc = null;
        try
        {
            doc = factory.newDocumentBuilder().parse(inputStream);
        }
        catch(Exception e)
        {
            throw new ESException(e);
        }
        buildElectionSpecification(doc.getFirstChild());
    }

    public ElectionSpecification(Node spec)
        throws ESException
    {
        buildElectionSpecification(spec);
    }

    public String getId()
    {
        return id;
    }

    public Hashtable<String, Section> getSections()
    {
        return sections;
    }

    public Section[] getOrderedSections()
    {
        int n = sections.size();
        Section ret[] = new Section[n];
        for(Enumeration<String> e = sections.keys(); e.hasMoreElements();)
        {
            Section s = sections.get(e.nextElement());
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
            String pathToSchemaFile = "org/gwu/voting/standardFormat/electionSpecification/ElectionSpecification.xsd";
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
        s = (new StringBuilder()).append(s).append(linePrefix).append("<").append(Constants.TAG_ELECTION_SPECIFICATION).append(" version=\"0.1\">").append(lineSufix).toString();
        s = (new StringBuilder()).append(s).append(linePrefix).append("\t<").append(Constants.TAG_ELECTIONINFO).append(" ").append(Constants.ATTRIBUTE_ID).append("=\"").append(id).append("\">").append(lineSufix).toString();
        s = (new StringBuilder()).append(s).append(linePrefix).append("\t\t<").append(Constants.TAG_SECTIONS).append(">").append(lineSufix).toString();
        for(Enumeration<Section> e = sections.elements(); e.hasMoreElements();)
            s = (new StringBuilder()).append(s).append(e.nextElement().toFortamedString((new StringBuilder()).append(linePrefix).append("\t\t\t").toString(), lineSufix)).toString();

        s = (new StringBuilder()).append(s).append(linePrefix).append("\t\t</").append(Constants.TAG_SECTIONS).append(">").append(lineSufix).toString();
        s = (new StringBuilder()).append(s).append(linePrefix).append("\t</").append(Constants.TAG_ELECTIONINFO).append(">").append(lineSufix).toString();
        s = (new StringBuilder()).append(s).append(linePrefix).append("</").append(Constants.TAG_ELECTION_SPECIFICATION).append(">").append(lineSufix).toString();
        return s;
    }

    private void buildElectionSpecification(Node spec)
        throws ESException
    {
        if(spec == null)
            throw new ESException("Need to construct a |election specification| from a node, but node is null");
        NodeList electionInfo = spec.getOwnerDocument().getElementsByTagName(Constants.TAG_ELECTIONINFO);
        NamedNodeMap attributes = electionInfo.item(0).getAttributes();
        Node idAttribute = attributes.getNamedItem(Constants.ATTRIBUTE_ID);
        id = idAttribute.getNodeValue();
        Section s = null;
        sections = new Hashtable<String, Section>();
        NodeList ss = spec.getOwnerDocument().getElementsByTagName(Constants.TAG_SECTION);
        for(int i = 0; i < ss.getLength(); i++)
        {
            try
            {
                s = new Section(ss.item(i));
            }
            catch(BasicException be)
            {
                throw new ESException(be);
            }
            String sID = s.getId();
            if(sections.get(sID) != null)
            {
                Hashtable oldQs = sections.get(sID).getQuestions();
                Hashtable newQs = s.getQuestions();
                String qID = null;
                for(Enumeration e = newQs.keys(); e.hasMoreElements();)
                {
                    oldQs.put(qID, newQs.get(qID));
                    qID = (String)e.nextElement();
                }

            } else
            {
                sections.put(sID, s);
            }
        }

    }

    String id;
    Hashtable<String, Section> sections;
}
