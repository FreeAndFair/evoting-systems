// Reversed by Rick using JAD decompiler with some tweaks
// Jad home page: http://www.geocities.com/kpdus/jad.html
// Decompiler options: packimports(3) 
// Source File Name:   Section.java

package org.scantegrity.common.ballotstandards.basic;

import java.io.Serializable;
import java.util.Enumeration;
import java.util.Hashtable;
import org.scantegrity.common.ballotstandards.Constants;
import org.scantegrity.common.ballotstandards.Util;
import org.scantegrity.common.ballotstandards.basic.exceptions.BasicException;
import org.w3c.dom.NamedNodeMap;
import org.w3c.dom.Node;

// Referenced classes of package org.scantegrity.common.ballotstandards.basic:
//            Question

public class Section
    implements Serializable
{

    /**
	 * 
	 */
	private static final long serialVersionUID = -2749065410695944590L;
	public Section()
    {
        possition = -1;
        questions = new Hashtable<String, Question>();
    }

    public Section(Node s)
        throws BasicException
    {
        possition = -1;
        if(s == null)
            throw new BasicException((new StringBuilder()).append("Need to construct a |").append(Constants.TAG_SECTION).append("| from a node, but node is null").toString());
        Util.eliminateFakeChilds(s);
        questions = new Hashtable<String, Question>();
        NamedNodeMap attributes = s.getAttributes();
        id = attributes.getNamedItem(Constants.ATTRIBUTE_ID).getNodeValue();
        Node posNode = attributes.getNamedItem(Constants.ATTRIBUTE_POSSITION);
        if(posNode != null)
            possition = Integer.parseInt(posNode.getNodeValue());
        for(Node node = s.getFirstChild().getFirstChild(); node != null; node = node.getNextSibling())
        {
            Question q = new Question(node);
            String qID = q.getId();
            if(questions.get(qID) != null)
                throw new BasicException((new StringBuilder()).append("Duplicate question ID |").append(qID).append("| in node |").append(Constants.TAG_SECTION).append("| with the ID |").append(id).append("|").toString());
            questions.put(qID, q);
        }

    }

    public Question[] getOrderedQuestions()
    {
        int n = questions.size();
        Question ret[] = new Question[n];
        for(Enumeration<String> e = questions.keys(); e.hasMoreElements();)
        {
            Question q = questions.get(e.nextElement());
            ret[q.getPossition() - 1] = q;
        }

        return ret;
    }

    public Hashtable<String, Question> getQuestions()
    {
        return questions;
    }

    public String getId()
    {
        return id;
    }

    public int getPossition()
    {
        return possition;
    }

    public void setPossition(int possition)
    {
        this.possition = possition;
    }

    public void setId(String id)
    {
        this.id = id;
    }

    public void setQuestions(Hashtable<String, Question> questions)
    {
        this.questions = questions;
    }

    public String toString()
    {
        return toFortamedString("", "\n");
    }

    public String toFortamedString(String linePrefix, String lineSufix)
    {
        String s = "";
        s = (new StringBuilder()).append(s).append(linePrefix).append("<").append(Constants.TAG_SECTION).append(" ").append(Constants.ATTRIBUTE_ID).append("=\"").append(id).append("\"").append(" ").append(Constants.ATTRIBUTE_POSSITION).append("=\"").append(possition).append("\">").append(lineSufix).toString();
        s = (new StringBuilder()).append(s).append(linePrefix).append("\t<").append(Constants.TAG_QUESTIONS).append(">").append(lineSufix).toString();
        for(Enumeration<Question> e = questions.elements(); e.hasMoreElements();)
            s = (new StringBuilder()).append(s).append(e.nextElement().toFortamedString((new StringBuilder()).append(linePrefix).append("\t\t").toString(), lineSufix)).toString();

        s = (new StringBuilder()).append(s).append(linePrefix).append("\t</").append(Constants.TAG_QUESTIONS).append(">").append(lineSufix).toString();
        s = (new StringBuilder()).append(s).append(linePrefix).append("</").append(Constants.TAG_SECTION).append(">").append(lineSufix).toString();
        return s;
    }

    String id;
    int possition;
    Hashtable<String, Question> questions;
}
