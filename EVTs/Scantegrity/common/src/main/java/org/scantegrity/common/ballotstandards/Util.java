// Reversed by Rick using JAD decompiler with some tweaks
// Jad home page: http://www.geocities.com/kpdus/jad.html
// Decompiler options: packimports(3) 
// Source File Name:   Util.java

package org.scantegrity.common.ballotstandards;

import java.io.File;
import java.util.jar.JarEntry;
import java.util.jar.JarFile;
import javax.xml.transform.stream.StreamSource;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;

public class Util
{

    public Util()
    {
    }

    public static boolean isTrueNode(Node node)
    {
        if(node == null)
            return false;
        if(node.getNodeName().compareTo("#comment") == 0)
            return false;
        if(node.getNodeName().compareTo("#text") == 0)
        {
            String value = node.getNodeValue();
            for(int i = 0; i < value.length(); i++)
            {
                char c = value.charAt(i);
                if(c != ' ' && c != '\t' && c != '\n')
                    return true;
            }

            return false;
        } else
        {
            return true;
        }
    }

    public static void eliminateFakeChilds(Node node)
    {
        NodeList childNodes = node.getChildNodes();
        if(childNodes == null)
            return;
        int length = childNodes.getLength();
        int currentNodeIndex = 0;
        for(int i = 0; i < length; i++)
        {
            Node childOneNode = childNodes.item(currentNodeIndex);
            if(!isTrueNode(childOneNode))
            {
                node.removeChild(childOneNode);
            } else
            {
                eliminateFakeChilds(childOneNode);
                currentNodeIndex++;
            }
        }

    }

    public static void printDebugNode(Node n)
    {
        System.out.println((new StringBuilder()).append("Type: ").append(n.getNodeType()).append(" Name: ").append(n.getNodeName()).append(" Value: ").append(n.getNodeValue()).toString());
    }

    public static StreamSource getStreamSource(String path)
        throws Exception
    {
        return new StreamSource(new File(path));
    }

    public static StreamSource getStreamSource(String jarPath, String relPath)
        throws Exception
    {
        JarFile jarFile = new JarFile(jarPath);
        java.io.InputStream inStream = jarFile.getInputStream(new JarEntry(relPath));
        return new StreamSource(inStream);
    }

    public static void main(String args[])
        throws Exception
    {
        getStreamSource("org/gwu/voting/standardFormat/", "electionSpecification/ElectionSpecification.xsd");
    }
}
