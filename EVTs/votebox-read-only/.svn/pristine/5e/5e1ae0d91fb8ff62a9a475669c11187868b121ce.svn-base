/**
  * This file is part of VoteBox.
  * 
  * VoteBox is free software: you can redistribute it and/or modify
  * it under the terms of the GNU General Public License version 3 as published by
  * the Free Software Foundation.
  * 
  * You should have received a copy of the GNU General Public License
  * along with VoteBox, found in the root of any distribution or
  * repository containing all or part of VoteBox.
  * 
  * THIS SOFTWARE IS PROVIDED BY WILLIAM MARSH RICE UNIVERSITY, HOUSTON,
  * TX AND IS PROVIDED 'AS IS' AND WITHOUT ANY EXPRESS, IMPLIED OR
  * STATUTORY WARRANTIES, INCLUDING, BUT NOT LIMITED TO, WARRANTIES OF
  * ACCURACY, COMPLETENESS, AND NONINFRINGEMENT.  THE SOFTWARE USER SHALL
  * INDEMNIFY, DEFEND AND HOLD HARMLESS RICE UNIVERSITY AND ITS FACULTY,
  * STAFF AND STUDENTS FROM ANY AND ALL CLAIMS, ACTIONS, DAMAGES, LOSSES,
  * LIABILITIES, COSTS AND EXPENSES, INCLUDING ATTORNEYS' FEES AND COURT
  * COSTS, DIRECTLY OR INDIRECTLY ARISING OUR OF OR IN CONNECTION WITH
  * ACCESS OR USE OF THE SOFTWARE.
 */

package preptool.model;

import java.io.File;
import java.io.IOException;
import java.util.HashMap;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerConfigurationException;
import javax.xml.transform.TransformerException;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.TransformerFactoryConfigurationError;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.NodeList;
import org.xml.sax.SAXException;

/**
 * Static methods for reading, writing, and formatting XML documents.
 * @author cshaw
 */
public class XMLTools {

	/**
	 * Adds a property element
	 * @param doc the document
	 * @param elt the element to add the property to
	 * @param name name of the property
	 * @param type type of the property
	 * @param value value of the property
	 */
	public static void addProperty(Document doc, Element elt, String name,
			String type, Object value) {
		Element propElt = doc.createElement("Property");
		propElt.setAttribute("name", name);
		propElt.setAttribute("type", type);
		propElt.setAttribute("value", value.toString());
		elt.appendChild(propElt);
	}
    
    /**
     * Adds a list property element
     * @param doc the document
     * @param elt the element to add the property to
     * @param name name of the property
     * @param type type of the property
     * @param values values of the property
     */
    public static void addListProperty(Document doc, Element elt, String name,
            String type, Object[] values) {
        Element propElt = doc.createElement("ListProperty");
        propElt.setAttribute("name", name);
        propElt.setAttribute("type", type);
        for (Object val: values) {
            Element listElt = doc.createElement("ListElement");
            listElt.setAttribute("value", val.toString());
            propElt.appendChild(listElt);
        }
        elt.appendChild(propElt);
    }

	/**
	 * Constructs a new document
	 * @return the new document
	 */
	public static Document createDocument() throws ParserConfigurationException {
		return DocumentBuilderFactory.newInstance().newDocumentBuilder()
				.newDocument();
	}

	/**
	 * Writes an XML tree to disk
	 * @param rootElt the root element
	 * @param file path of the file to write to
	 */
	public static void writeXML(Element rootElt, String file)
			throws TransformerConfigurationException, IllegalArgumentException,
			TransformerFactoryConfigurationError, TransformerException {
		rootElt.normalize();
		Transformer xformer = TransformerFactory.newInstance().newTransformer();
		xformer.setOutputProperty("indent", "yes");
		DOMSource d = new DOMSource(rootElt);
		StreamResult r = new StreamResult(new File(file));
		xformer.transform(d, r);
	}

	/**
	 * Returns a HashMap of all of the properties of an element
	 * @param elt the element
	 * @return a HashMap of the properties
	 */
	public static HashMap<String, Object> getProperties(Element elt) {
		HashMap<String, Object> properties = new HashMap<String, Object>();
		NodeList list = elt.getElementsByTagName("Property");
		for (int i = 0; i < list.getLength(); i++) {
			Element prop = (Element) list.item(i);
			if (prop.getAttribute("type").equals("String"))
				properties.put(prop.getAttribute("name"), prop
						.getAttribute("value"));
			if (prop.getAttribute("type").equals("Integer"))
				properties.put(prop.getAttribute("name"), Integer.parseInt(prop
						.getAttribute("value")));
			if (prop.getAttribute("type").equals("Boolean"))
				properties.put(prop.getAttribute("name"), Boolean
						.parseBoolean(prop.getAttribute("value")));
		}
		return properties;
	}

	/**
	 * Reads an XML tree from disk into a document
	 * @param file path of the file
	 * @return the document
	 */
	public static Document readXML(String file)
			throws ParserConfigurationException, SAXException, IOException {
		DocumentBuilder builder = DocumentBuilderFactory.newInstance()
				.newDocumentBuilder();
		return builder.parse(new File(file));
	}

}
