// Reversed by Rick using JAD decompiler with some tweaks
// Jad home page: http://www.geocities.com/kpdus/jad.html
// Decompiler options: packimports(3) 
// Source File Name:   Question.java

package org.scantegrity.common.ballotstandards.basic;

import java.io.*;
import java.util.Enumeration;
import java.util.Hashtable;
import javax.xml.parsers.DocumentBuilderFactory;
import org.scantegrity.common.ballotstandards.*;
import org.scantegrity.common.ballotstandards.basic.exceptions.BasicException;
import org.w3c.dom.*;

// Referenced classes of package org.scantegrity.common.ballotstandards.basic:
//            Answer

public class Question
    implements Serializable
{

    /**
	 * 
	 */
	private static final long serialVersionUID = -2160670384656717565L;
	public Question()
    {
        id = null;
        possition = -1;
        typeOfAnswer = null;
        answers = null;
        texts = null;
        audios = null;
        images = null;
        min = -1;
        max = -1;
        points = -1F;
        answers = new Hashtable<String, Answer>();
        audios = new Hashtable<Integer, String>();
        images = new Hashtable<Integer, String>();
        texts = new Hashtable<Integer, String>();
    }

    public Question(String id, String typeOfA)
    {
        this();
        this.id = id;
        typeOfAnswer = typeOfA;
    }

    public Question(Node q)
        throws BasicException
    {
        this();
        if(q == null)
            throw new BasicException((new StringBuilder()).append("Need to construct a |").append(Constants.TAG_QUESTION).append("|from a node, but node is null").toString());
        Util.eliminateFakeChilds(q);
        NamedNodeMap attributes = q.getAttributes();
        id = attributes.getNamedItem(Constants.ATTRIBUTE_ID).getNodeValue();
        Node toac = attributes.getNamedItem(Constants.ATTRIBUTE_TYPE_OF_ANSWER);
        if(toac != null)
            typeOfAnswer = toac.getNodeValue();
        toac = attributes.getNamedItem(Constants.ATTRIBUTE_POINTS);
        if(toac != null)
            points = Float.parseFloat(toac.getNodeValue());
        toac = attributes.getNamedItem(Constants.ATTRIBUTE_POSSITION);
        if(toac != null)
            possition = Integer.parseInt(toac.getNodeValue());
        for(Node child = q.getFirstChild(); child != null; child = child.getNextSibling())
        {
            String nodeName = child.getNodeName();
            if(nodeName.compareTo(Constants.TAG_ANSWERS) == 0)
            {
                for(Node answer = child.getFirstChild(); answer != null; answer = answer.getNextSibling())
                {
                    Answer qAnswer = new Answer(answer);
                    String aID = qAnswer.getId();
                    if(answers.get(aID) != null)
                        throw new BasicException((new StringBuilder()).append("Duplicate answer ID |").append(aID).append("| in question |").append(id).append("|").toString());
                    answers.put(aID, qAnswer);
                }

            }
            if(nodeName.compareTo(Constants.TAG_TEXTS) == 0)
            {
                Node grandchild = child.getFirstChild();
                int textNumber = 0;
                for(; grandchild != null; grandchild = grandchild.getNextSibling())
                {
                    String grandchildName = grandchild.getNodeName();
                    if(grandchildName.compareTo(Constants.TAG_TEXT) == 0)
                        texts.put(new Integer(textNumber++), grandchild.getFirstChild().getNodeName());
                }

            }
            if(nodeName.compareTo(Constants.TAG_AUDIOS) == 0)
            {
                Node grandchild = child.getFirstChild();
                int audioNumber = 0;
                for(; grandchild != null; grandchild = grandchild.getNextSibling())
                {
                    String grandchildName = grandchild.getNodeName();
                    if(grandchildName.compareTo(Constants.TAG_AUDIO) == 0)
                        audios.put(new Integer(audioNumber++), grandchild.getFirstChild().getNodeName());
                }

            }
            if(nodeName.compareTo(Constants.TAG_IMAGES) == 0)
            {
                Node grandchild = child.getFirstChild();
                int imageNumber = 0;
                for(; grandchild != null; grandchild = grandchild.getNextSibling())
                {
                    String grandchildName = grandchild.getNodeName();
                    if(grandchildName.compareTo(Constants.TAG_IMAGE) == 0)
                        images.put(new Integer(imageNumber++), grandchild.getFirstChild().getNodeName());
                }

            }
            if(nodeName.compareTo(Constants.TAG_DEPENDS) != 0);
        }

        attributes = q.getAttributes();
        int max = privGetMax(attributes);
        if(max > answers.size())
            throw new BasicException((new StringBuilder()).append("Node |").append(Constants.ATTRIBUTE_TYPE_OF_ANSWER).append("| has a value for the |").append(Constants.ATTRIBUTE_MAX_ANSWERS).append("| attribute greater then the number of answers").toString());
        this.max = max;
        int min = privGetMin(attributes);
        if(min > answers.size())
        {
            throw new BasicException((new StringBuilder()).append("Node |").append(Constants.ATTRIBUTE_TYPE_OF_ANSWER).append("| has a value for the |").append(Constants.ATTRIBUTE_MIN_ANSWERS).append("| attribute greater then the number of answers").toString());
        } else
        {
            this.min = min;
            return;
        }
    }

    public Hashtable<String, Answer> getAnswers()
    {
        return answers;
    }

    public String getId()
    {
        return id;
    }

    public Answer[] getOrderedAnswers()
    {
        int n = answers.size();
        Answer ret[] = new Answer[n];
        for(Enumeration<String> e = answers.keys(); e.hasMoreElements();)
        {
            Answer a = answers.get(e.nextElement());
            ret[a.getPossition() - 1] = a;
        }

        return ret;
    }

    public int getPossition()
    {
        return possition;
    }

    public void setPossition(int possition)
    {
        this.possition = possition;
    }

    public float getPoints()
    {
        return points;
    }

    public int getMax()
    {
        return max;
    }

    public void setMax(int max)
    {
        this.max = max;
    }

    public int getMin()
    {
        return min;
    }

    public void setMin(int min)
    {
        this.min = min;
    }

    public String getTypeOfAnswer()
    {
        return typeOfAnswer;
    }

    public void setTypeOfAnswer(String typeOfAnswer)
    {
        this.typeOfAnswer = typeOfAnswer;
    }

    public void setAnswers(Hashtable<String, Answer> answers)
    {
        this.answers = answers;
    }

    public void setId(String id)
    {
        this.id = id;
    }

    public void setPoints(float points)
    {
        this.points = points;
    }

    public Hashtable<Integer, String> getAudios()
    {
        return audios;
    }

    public void setAudios(Hashtable<Integer, String> audios)
    {
        this.audios = audios;
    }

    public Hashtable<Integer, String> getImages()
    {
        return images;
    }

    public void setImages(Hashtable<Integer, String> images)
    {
        this.images = images;
    }

    public Hashtable<Integer, String> getTexts()
    {
        return texts;
    }

    public void setTexts(Hashtable<Integer, String> texts)
    {
        this.texts = texts;
    }

    public String toString()
    {
        return toFortamedString("", "\n");
    }

    public String toFortamedString(String linePrefix, String lineSufix)
    {
        String s = "";
        s = (new StringBuilder()).append(s).append(linePrefix).append("<").append(Constants.TAG_QUESTION).append(" ").append(Constants.ATTRIBUTE_ID).append("=\"").append(id).append("\"").append(" ").append(Constants.ATTRIBUTE_POSSITION).append("=\"").append(possition).append("\"").toString();
        if(typeOfAnswer != null)
            s = (new StringBuilder()).append(s).append(" ").append(Constants.ATTRIBUTE_TYPE_OF_ANSWER).append("=\"").append(typeOfAnswer).append("\"").toString();
        if(min > 0)
            s = (new StringBuilder()).append(s).append(" ").append(Constants.ATTRIBUTE_MIN_ANSWERS).append("=\"").append(min).append("\"").toString();
        if(max > 0)
            s = (new StringBuilder()).append(s).append(" ").append(Constants.ATTRIBUTE_MAX_ANSWERS).append("=\"").append(max).append("\"").toString();
        if(typeOfAnswer != null && typeOfAnswer.compareTo(Constants.DISTRIBUTE_POINTS) == 0)
            s = (new StringBuilder()).append(s).append(" ").append(Constants.ATTRIBUTE_POINTS).append("=\"").append(points).append("\"").toString();
        s = (new StringBuilder()).append(s).append(">").append(lineSufix).toString();
        s = (new StringBuilder()).append(s).append(linePrefix).append("\t<").append(Constants.TAG_ANSWERS).append(">").append(lineSufix).toString();
        for(Enumeration<Answer> e = answers.elements(); e.hasMoreElements();)
            s = (new StringBuilder()).append(s).append(e.nextElement().toFortamedString((new StringBuilder()).append(linePrefix).append("\t\t").toString(), lineSufix)).toString();

        s = (new StringBuilder()).append(s).append(linePrefix).append("\t</").append(Constants.TAG_ANSWERS).append(">").append(lineSufix).toString();
        s = (new StringBuilder()).append(s).append(linePrefix).append("</").append(Constants.TAG_QUESTION).append(">").append(lineSufix).toString();
        return s;
    }

    private int privGetMax(NamedNodeMap attributes)
    {
        Node maxAttribute = attributes.getNamedItem(Constants.ATTRIBUTE_MAX_ANSWERS);
        if(maxAttribute != null)
            return Integer.parseInt(maxAttribute.getNodeValue());
        if(typeOfAnswer == null)
            return -1;
        if(typeOfAnswer.compareTo(Constants.ONE_ANSWER) == 0)
            return 1;
        else
            return answers.size();
    }

    private int privGetMin(NamedNodeMap attributes)
    {
        Node minAttribute = attributes.getNamedItem(Constants.ATTRIBUTE_MIN_ANSWERS);
        if(minAttribute != null)
            return Integer.parseInt(minAttribute.getNodeValue());
        return typeOfAnswer != null ? 1 : -1;
    }

    public static void main(String argv[])
        throws Exception
    {
        if(argv.length < 1)
        {
            System.out.println("No Parameters. The parameters are : path_to_the_xml_file [path_to_the_schema_file]");
            return;
        }
        DocumentBuilderFactory factory = DocumentBuilderFactory.newInstance();
        Document doc = factory.newDocumentBuilder().parse(new File(argv[0]));
        if(argv.length > 1)
        {
            SchemaChecker schemaChecker = new SchemaChecker(argv[1]);
            schemaChecker.validate(doc);
            System.out.println("The file is sintacticly valid");
        }
        Question question = new Question(doc.getFirstChild());
        System.out.println(question);
    }

    String id;
    int possition;
    String typeOfAnswer;
    Hashtable<String, Answer> answers;
    Hashtable<Integer, String> texts;
    Hashtable<Integer, String> audios;
    Hashtable<Integer, String> images;
    int min;
    int max;
    float points;
}
