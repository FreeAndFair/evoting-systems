// Reversed by Rick using JAD decompiler with some tweaks
// Jad home page: http://www.geocities.com/kpdus/jad.html
// Decompiler options: packimports(3) 
// Source File Name:   SchemaChecker.java

package org.scantegrity.common.ballotstandards;

import java.io.*;
import javax.xml.parsers.*;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamSource;
import javax.xml.validation.*;
import org.w3c.dom.Document;
import org.xml.sax.SAXException;

public class SchemaChecker
{

    public SchemaChecker()
    {
        validator = null;
    }

    public SchemaChecker(String pathToSchemaFile)
        throws Exception
    {
        validator = null;
        SchemaFactory factory = SchemaFactory.newInstance("http://www.w3.org/2001/XMLSchema");
        javax.xml.transform.Source schemaSource = new StreamSource(new File(pathToSchemaFile));
        Schema schema = factory.newSchema(schemaSource);
        validator = schema.newValidator();
    }

    public SchemaChecker(InputStream schemaFile)
        throws SAXException
    {
        validator = null;
        SchemaFactory factory = SchemaFactory.newInstance("http://www.w3.org/2001/XMLSchema");
        javax.xml.transform.Source schemaSource = new StreamSource(schemaFile);
        Schema schema = factory.newSchema(schemaSource);
        validator = schema.newValidator();
    }

    public void validate(Document doc)
        throws SAXException, IOException
    {
        validator.validate(new DOMSource(doc));
    }

    public void validate(String pathToFile)
        throws SAXException, IOException, ParserConfigurationException
    {
        DocumentBuilderFactory factory = DocumentBuilderFactory.newInstance();
        Document doc = factory.newDocumentBuilder().parse(new File(pathToFile));
        validate(doc);
    }

	Validator validator;
}
