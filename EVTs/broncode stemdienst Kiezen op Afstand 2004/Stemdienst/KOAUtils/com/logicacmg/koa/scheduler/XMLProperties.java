/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.scheduler.Scheduler.java
  *
  * -----------------------------------------------------------------------
  * 
  *  (c) 2003  Ministerie van Binnenlandse Zaken en Koninkrijkrelaties
  *
  *  Project		: Kiezen Op Afstand (KOA)
  *  Project Number	: ECF-2651
  *  
  *  History:
  *  Version	Date		Name		Reason
  * ---------------------------------------------------------
  *  0.1		25-04-2003	MKu			First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.scheduler;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.util.Enumeration;
import java.util.Properties;
import java.util.Stack;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.SAXParser;
import javax.xml.parsers.SAXParserFactory;

import org.apache.xalan.serialize.DOMSerializer;
import org.w3c.dom.Comment;
import org.w3c.dom.DOMException;
import org.w3c.dom.Document;
import org.w3c.dom.Node;
import org.xml.sax.Attributes;
import org.xml.sax.SAXException;

import com.logica.eplatform.util.LogHelper;
/**
 * XML properties conversion object.
 * This object is specifically used for the scheduler
 * 
 * @author KuijerM
 */
public class XMLProperties extends Properties implements java.io.Serializable
{
	/**
	 * Inner class handling the XML to property translation
	 */
	class XPContentHandler extends org.xml.sax.helpers.DefaultHandler
	{
		Stack tagStack = new Stack();
		boolean rootTag = true;
		/**
		 * Constructor for the XP content handler
		 */
		public XPContentHandler()
		{
			tagStack.push("");
		}
		/**
		 * Start handling the XML element
		 * 
		 * @param uri The uri
		 * @param localName The localname
		 * @param qName The name of the element
		 * @param attributes The attributes in the element
		 * 
		 * @throws SAXException When something goes wrong handling the Element
		 * 
		 */
		public void startElement(
			java.lang.String uri,
			java.lang.String localName,
			java.lang.String qName,
			Attributes attributes)
			throws SAXException
		{
			if (rootTag)
			{
				rootTag = false;
			}
			else
			{
				tagStack.push(
					tagStack.peek().equals("")
						? qName
						: tagStack.peek() + "_" + qName);
			}
		}
		/**
		 * Handle the characters within the element
		 * 
		 * @param chars The characters in the element
		 * @param start The start position
		 * @param len the length of the character array
		 * 
		 */
		public void characters(char[] chars, int start, int len)
		{
			String key = (String) tagStack.peek();
			String value = new String(chars, start, len);
			if (value.trim().length() > 0)
			{
				setProperty(key, value);
			}
		}
		/**
		 * Handle the end of the element
		 * 
		* @param uri The uri
		* @param localName The localname
		* @param qName The name of the element
		 * 
		* @throws SAXException When something goes wrong handling the Element
		 * 
		 */
		public void endElement(
			java.lang.String uri,
			java.lang.String localName,
			java.lang.String qName)
			throws SAXException
		{
			tagStack.pop();
		}
	}
	/**
	 * Constructor for the XML properties
	 * 
	 */
	public XMLProperties(Properties props)
	{
		super(props);
	}
	/**
	 * Loads the XML when contained in a stream
	 * 
	 * @param is The inputstream containing the XML
	 * 
	 * @throws Exception When something goes wrong loading the XML
	 * 
	 */
	public void loadXMLStream(InputStream is) throws Exception
	{
		SAXParser parser = SAXParserFactory.newInstance().newSAXParser();
		parser.parse(is, new XPContentHandler());
	}
	/**
	 * Loads the XML from a String
	 * 
	 * @param xmlString The String containing the xml
	 * 
	 * @throws Exception When something goes wrong loading the XML
	 * 
	 */
	public void loadXMLString(String xmlString) throws Exception
	{
		java.io.ByteArrayInputStream bais =
			new java.io.ByteArrayInputStream(xmlString.getBytes());
		loadXMLStream(bais);
	}
	/**
	 * Loads the node
	 */
	public void loadNode(Node node) throws Exception
	{
	}
	/**
	 * Stores the XML from the properties in the outputstream 
	 * With the specified header and root element.
	 * 
	 * @param os The outputstream to write to
	 * @param header The header to use in the top of the document
	 * @param root The root element to use
	 * 
	 * @throws IOException	When something goes wrong in IO for outputstream
	 * @throws Exception 	All other exceptions
	 */
	public void storeXML(OutputStream os, String header, String root)
		throws IOException, Exception
	{
		//Create a document
		DocumentBuilder db = null;
		DocumentBuilderFactory factory = null;
		try
		{
			factory = DocumentBuilderFactory.newInstance();
			db = (DocumentBuilder) factory.newDocumentBuilder();
		}
		catch (Exception e)
		{
			LogHelper.trace(
				LogHelper.TRACE,
				"[XMLProperties]: Exception while making new DocumentBuilder: "
					+ e.getMessage());
			throw new IllegalStateException("Parser Configuration error!");
		}
		Document doc = db.newDocument();
		Node rootNode = doc.createElement(root);
		doc.appendChild(rootNode);
		//Store the properties file in the document as node
		storeXML(rootNode);
		//Write header as commentnode
		if (header != "")
		{
			Comment com = doc.createComment(header);
			doc.insertBefore(com, doc.getFirstChild());
		}
		//Serialize document for outputstream
		DOMSerializer ds =
			new XMLSerializer(os, new OutputFormat("XML", "UTF-8", true))
				.asDOMSerializer();
		ds.serialize(doc);
	}
	/**
	 * Stores the XML from the properties in the node.
	 * 
	 * @param baseNode The base node to use
	 * 
	 * @throws IllegalStateException When the node is in a illegal state
	 * @throws Exception 			 All other exceptions
	 */
	public void storeXML(Node baseNode) throws IllegalStateException, Exception
	{
		String property;
		String waarde;
		Enumeration propslist;
		String nodename = "";
		Node parentNode = null;
		Node childNode = null;
		Node firstChild = null;
		Node nextChild = null;
		Node lastChild = null;
		boolean nodegevonden = false;
		Document ownDoc;
		// Set the ownerdocument
		if (baseNode.getNodeType() == Node.DOCUMENT_NODE)
		{
			ownDoc = (Document) baseNode;
		}
		else
		{
			ownDoc = baseNode.getOwnerDocument();
		}
		propslist = this.propertyNames();
		while (propslist.hasMoreElements())
		{
			// Get the first property
			property = (String) propslist.nextElement();
			waarde = this.getProperty(property);
			// Chop the property and put it in an Array
			parentNode = baseNode;
			while (true)
			{
				nodegevonden = false;
				// if the property contains a "_" than the property is devided in multiple nodes"
				if (property.indexOf("_") != -1)
				{
					nodename = property.substring(0, property.indexOf("_"));
					property =
						property.substring(
							property.indexOf("_") + 1,
							property.length());
					// Check if the property's first charachter is not a numeric one. This needs to be done because
					// xml-tags that start with a numeric character are invalid
					if (Character.isDigit(nodename.charAt(0)))
					{
						// prefix the property with an 'n', this only happens for badly non-xml-compliant keys
						nodename = "n" + nodename;
					}
					// See if there is a node like this already
					// We know the level we're in and we know the parentnodename
					nextChild = parentNode.getFirstChild();
					lastChild = parentNode.getLastChild();
					while (nextChild != null)
					{
						if (nextChild.getNodeName().equals(nodename))
						{
							parentNode = nextChild;
							nodegevonden = true;
							break;
						}
						nextChild = nextChild.getNextSibling();
					}
					// End of Search
					if (!nodegevonden)
					{
						childNode = ownDoc.createElement(nodename);
						try
						{
							parentNode.appendChild(childNode);
						}
						catch (Exception e)
						{
							// Throws exception when trying to append more than 1 node to ownDoc
							throw new IllegalStateException("Wrong properties format: multiple rootnodes.");
						}
						parentNode = childNode;
					}
				}
				else
				{
					nodename = property;
					// Check if the property's first charachter is not a numeric one. This needs to be done because
					// xml-tags that start with a numeric character are invalid
					if (Character.isDigit(nodename.charAt(0)))
					{
						// prefix the property with an 'n', this only happens for badly non-xml-compliant keys
						nodename = "n" + nodename;
					}
					try
					{
						childNode = ownDoc.createElement(nodename);
						childNode.appendChild(ownDoc.createTextNode(waarde));
						parentNode.appendChild(childNode);
					}
					catch (DOMException de)
					{
						LogHelper.trace(
							LogHelper.TRACE,
							"XMLProperties.init(): exit with DOMException: "
								+ de.getMessage());
						LogHelper.trace(
							LogHelper.TRACE,
							"[XMLProps] StoreXML: nodename "
								+ nodename
								+ " values "
								+ waarde);
						LogHelper.trace(
							LogHelper.TRACE,
							"[XMLProps] StoreXML: exception" + de);
						throw new Exception("default");
					}
					break;
				}
			}
		}
	}
}