// Reversed by Rick using JAD decompiler with some tweaks
// Jad home page: http://www.geocities.com/kpdus/jad.html
// Decompiler options: packimports(3) 
// Source File Name:   Answer.java

package org.scantegrity.common.ballotstandards.basic;

import java.io.Serializable;
import java.util.Hashtable;
import org.scantegrity.common.ballotstandards.Constants;
import org.scantegrity.common.ballotstandards.Util;
import org.scantegrity.common.ballotstandards.basic.exceptions.BasicException;
import org.w3c.dom.NamedNodeMap;
import org.w3c.dom.Node;

public class Answer
    implements Serializable
{

    /**
	 * 
	 */
	private static final long serialVersionUID = 217077100482481161L;
	public Answer()
    {
        id = null;
        possition = -1;
        texts = null;
        audios = null;
        images = null;
        points = 0.0F;
        audios = new Hashtable<Integer, String>();
        images = new Hashtable<Integer, String>();
        texts = new Hashtable<Integer, String>();
    }

    public Answer(String id)
    {
        this();
        this.id = id;
    }

    public Answer(Node a)
        throws BasicException
    {
        this();
        if(a == null)
            throw new BasicException((new StringBuilder()).append("Need to construct an |").append(Constants.TAG_ANSWER).append("|from a node, but node is null").toString());
        Util.eliminateFakeChilds(a);
        NamedNodeMap attributes = a.getAttributes();
        id = attributes.getNamedItem(Constants.ATTRIBUTE_ID).getNodeValue();
        Node toac = attributes.getNamedItem(Constants.ATTRIBUTE_POINTS);
        if(toac != null)
            points = Float.parseFloat(toac.getNodeValue());
        toac = attributes.getNamedItem(Constants.ATTRIBUTE_POSSITION);
        if(toac != null)
            possition = Integer.parseInt(toac.getNodeValue());
        for(Node child = a.getFirstChild(); child != null; child = child.getNextSibling())
        {
            String nodeName = child.getNodeName();
            Node grandchild;
            if(nodeName.compareTo(Constants.TAG_TEXTS) == 0)
            {
                grandchild = child.getFirstChild();
                int textNumber = 0;
                for(; grandchild != null; grandchild = grandchild.getNextSibling())
                {
                    String grandchildName = grandchild.getNodeName();
                    if(grandchildName.compareTo(Constants.TAG_TEXT) == 0)
                        texts.put(new Integer(textNumber++), grandchild.getFirstChild().getNodeValue().trim());
                }

            }
            if(nodeName.compareTo(Constants.TAG_AUDIOS) == 0)
            {
                grandchild = child.getFirstChild();
                int audioNumber = 0;
                for(; grandchild != null; grandchild = grandchild.getNextSibling())
                {
                    String grandchildName = grandchild.getNodeName();
                    if(grandchildName.compareTo(Constants.TAG_AUDIO) == 0)
                        audios.put(new Integer(audioNumber++), grandchild.getFirstChild().getNodeValue().trim());
                }

            }
            if(nodeName.compareTo(Constants.TAG_IMAGES) != 0)
                continue;
            grandchild = child.getFirstChild();
            int imageNumber = 0;
            for(; grandchild != null; grandchild = grandchild.getNextSibling())
            {
                String grandchildName = grandchild.getNodeName();
                if(grandchildName.compareTo(Constants.TAG_IMAGE) == 0)
                    images.put(new Integer(imageNumber++), grandchild.getFirstChild().getNodeValue().trim());
            }

        }

    }

    public Hashtable<Integer, String> getAudios()
    {
        return audios;
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

    public Hashtable<Integer, String> getImages()
    {
        return images;
    }

    public Hashtable<Integer, String> getTexts()
    {
        return texts;
    }

    public float getPoints()
    {
        return points;
    }

    public void setPoints(float points)
    {
        this.points = points;
    }

    public float addPoints(float p)
    {
        float pp = points;
        points += p;
        return pp;
    }

    public void setAudios(Hashtable<Integer, String> audios)
    {
        this.audios = audios;
    }

    public void setId(String id)
    {
        this.id = id;
    }

    public void setImages(Hashtable<Integer, String> images)
    {
        this.images = images;
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
        String s = (new StringBuilder()).append(linePrefix).append("<").append(Constants.TAG_ANSWER).append(" ").append(Constants.ATTRIBUTE_ID).append("=\"").append(id).append("\"").append(" ").append(Constants.ATTRIBUTE_POSSITION).append("=\"").append(possition).append("\"").toString();
        if(points > -1F)
            s = (new StringBuilder()).append(s).append(" ").append(Constants.ATTRIBUTE_POINTS).append("=\"").append(points).append("\"").toString();
        s = (new StringBuilder()).append(s).append("/>").append(lineSufix).toString();
        return s;
    }

    String id;
    int possition;
    Hashtable<Integer, String> texts;
    Hashtable<Integer, String> audios;
    Hashtable<Integer, String> images;
    float points;
}
