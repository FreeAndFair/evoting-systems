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

package votebox.middle.ballot;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import javax.xml.XMLConstants;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.transform.TransformerConfigurationException;
import javax.xml.transform.TransformerException;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.dom.DOMResult;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamSource;
import javax.xml.validation.SchemaFactory;
import org.w3c.dom.Document;
import org.w3c.dom.NamedNodeMap;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;
import org.xml.sax.SAXException;

import votebox.middle.IBallotVars;
import votebox.middle.Properties;
import votebox.middle.UnknownFormatException;
import votebox.middle.UnknownTypeException;

/**
 * This class encapsulates the ballot XML parser. The ballot xml stores model
 * content information -- information about races, candidates, ballot
 * informatin, etc. This class's job is translate this information into a Ballot
 * object. This class might be better thought of as a Ballot deserializer, but
 * we have avoided this term so as not to mislead the reader into thinking that
 * we are using java object serialization.<br>
 * <br>
 * To deserialize a Ballot object, this class first uses java's xerces wrapper
 * to parse the ballot xml file into a w3c dom tree. This dom tree is first
 * validated with our schema and then interpreted recursively from the top down.
 * 
 * @author derrley
 * 
 */
public class BallotParser {

    /**
     * As we parse the dom tree, when we encounter new card elements we add them
     * to this hashmap. Each card element in this hash map is mapped by the
     * string representation of its uid.
     */
    private HashMap<String, SelectableCardElement> _elements;

    /**
     * This is the public constructor for BallotParser. It does nothing.
     */
    public BallotParser() {}

    /**
     * This is the core method for the ballot parser. Call this method to
     * translate a ballot xml file to a dom tree (as an intermediate
     * representation), then, primarily, to a ballot object.
     * 
     * @param vars
     *            The ballot parser will use this global parameters
     *            encapsulation to find where the ballot xml is stored.
     * @return This method returns the Ballot object which represents our dom
     *         tree.
     * @throws Exception
     *             This method throws an exception if the ballot parser
     *             encountered any problems translating the tree.
     */
    public Ballot getBallot(IBallotVars vars) throws BallotParserException {
        // init fields
        _elements = new HashMap<String, SelectableCardElement>();

        // document = new Document(); // sometimes patterns suck
        Document document;
        try {
            document = DocumentBuilderFactory.newInstance()
                    .newDocumentBuilder().newDocument();
        }
        catch (ParserConfigurationException e) {
            throw new BallotParserException(
                    "Internal Error, Could not get a new 'Document'.", e );
        }

        // parse the ballot xml -> dom tree
        try {
            TransformerFactory.newInstance().newTransformer().transform(
                new StreamSource( new File( vars.getBallotFile() ) ),
                new DOMResult( document ) );
        }
        catch (TransformerConfigurationException e) {
            throw new BallotParserException(
                    "InternalError. Could not configure the 'transformer' correctly.",
                    e );
        }
        catch (TransformerException e) {
            throw new BallotParserException(
                    "Could not parse the ballot's XML file. This is most likely because your ballot XML is malformed.",
                    e );
        }

        // validate the dom tree against our ballot schema.
        try {
            SchemaFactory.newInstance( XMLConstants.W3C_XML_SCHEMA_NS_URI )
                    .newSchema( vars.getBallotSchema() ).newValidator()
                    .validate( new DOMSource( document ) );
        }
        catch (SAXException e) {
            throw new BallotParserException(
                    "Could not validate the ballot XML against the schema.", e );
        }
        catch (IOException e) {
            throw new BallotParserException(
                    "Internal Error, Could not load the schema against which the ballot's XML should be validated.",
                    e );
        }

        // translate dom tree -> Ballot
        return parseBallot( document.getElementsByTagName( "Ballot" ).item( 0 ) );
    }

    /**
     * This method interprets a given dom node as being of the ballot type. This
     * method will convert the given dom node to a Ballot object
     * 
     * @param node
     *            This is the dom node that represents the ballot.
     * @return This method returns the ballot object that is represented by the
     *         given dom node.
     * @throws Exception
     *             This method throws an exception if the ballot parser
     *             encountered any problems translating the tree.
     */
    private Ballot parseBallot(Node node) throws BallotParserException {
        NodeList children = node.getChildNodes();
        ArrayList<Card> cards = new ArrayList<Card>();
        Properties properties = new Properties();

        // Children can either be properties or pages
        for (int lcv = 0; lcv < children.getLength(); lcv++) {
            Node child = children.item( lcv );

            if (child.getNodeName().equals( "Property" ))
                parseProperties( child, properties );
            else if (child.getNodeName().equals( "ListProperty" ))
                parseListProperties( child, properties );
            else if (child.getNodeName().equals( "Card" ))
                cards.add( parseCard( child ) );
            else if (child.getNodeName().equals( "#text" ))
                ;// Do nothing
            else
                throw new BallotParserException(
                        "I don't recognize " + child.getNodeName()
                                + " as being a Property or Page.", null );
        }

        List<List<String>> raceGroups = new ArrayList<List<String>>();
        for(Card card : cards){
        	Properties cardProps = card.getProperties();
        	if(cardProps.contains(Properties.RACE_GROUP)){
        		try{
        			raceGroups.add(cardProps.getStringList(Properties.RACE_GROUP));
        		}catch(Exception e){
        			throw new BallotParserException(e.getMessage(), null);
        		}
        	}//if
        }
        
        return new Ballot(cards, properties, _elements, raceGroups);
    }

    /**
     * This method is a helper method to parseBallot. It is called when a "Card"
     * node is encountered in the dom tree.
     * 
     * @param node
     *            This is the dom node that is a card node.
     * @return This method returns the card that is represented by the given dom
     *         node.
     * @throws Exception
     *             This method throws an exception if the ballot parser
     *             encountered any problems translating the tree.
     */
    private Card parseCard(Node node) throws BallotParserException {
        NodeList children = node.getChildNodes();
        ArrayList<SelectableCardElement> elements = new ArrayList<SelectableCardElement>();
        Properties properties = new Properties();

        for (int lcv = 0; lcv < children.getLength(); lcv++) {
            Node child = children.item( lcv );

            if (child.getNodeName().equals( "Property" ))
                parseProperties( child, properties );
            else if (child.getNodeName().equals( "ListProperty" ))
                parseListProperties( child, properties );
            else if (child.getNodeName().equals( "CardElement" )
                    || child.getNodeName().equals( "SelectableCardElement" )) {
                elements.add( parseElement( child ) );
            }
            else if (child.getNodeName().equals( "#text" ))
                ; // Do Nothing
            else
                throw new BallotParserException(
                        "I dont recognize "
                                + child.getNodeName()
                                + " as being a Property, CardElement, or SelectableCardElement",
                        null );
        }

        String uniqueID = node.getAttributes().getNamedItem( "uid" )
                .getNodeValue();

        return new Card( uniqueID, properties, elements );
    }

    /**
     * This method is a helper method to parseCard. It is called when a
     * SelectableCardElement or CardElement is encountered in the dom tree.
     * 
     * @param node
     *            This is the dom node which represents the element
     * @return This method returns the new element which represents the given
     *         dom node.
     * @throws Exception
     *             This method throws an exception if the ballot parser
     *             encountered any problems translating the tree.
     */
    private SelectableCardElement parseElement(Node node)
            throws BallotParserException {
        NamedNodeMap nodeAttributes = node.getAttributes();
        NodeList children = node.getChildNodes();

        String uniqueID = nodeAttributes.getNamedItem( "uid" ).getNodeValue();

        // Parse all the properties.
        Properties properties = new Properties();
        for (int lcv = 0; lcv < children.getLength(); lcv++) {
            Node child = children.item( lcv );

            if (child.getNodeName().equals( "Property" ))
                parseProperties( child, properties );
            else if (child.getNodeName().equals( "ListProperty" ))
                parseListProperties( child, properties );
            else if (child.getNodeName().equals( "#text" ))
                ; // Do nothing
            else
                throw new BallotParserException( "I dont recgonize "
                        + child.getNodeName() + " as a property.", null );
        }

        // Create the new card element.
        SelectableCardElement element = null;
        if (node.getNodeName().equals( "CardElement" )) {
            throw new BallotParserException(
                    "The use of CardElements has been disallowed. Please do not include non-selectable elements in the ballot, but only in the layout",
                    null );
        }
        else {
            element = new SelectableCardElement( uniqueID, properties );
        }

        // Make sure there are no duplicates
        if (_elements.containsKey( uniqueID ))
            throw new BallotParserException( "The unique ID " + uniqueID
                    + " was declared more than once in the ballot's XML", null );

        _elements.put( uniqueID, element );
        return element;
    }

    /**
     * This is a helper method to parseBallot, parseCard, and parseElement. It
     * is called when a dom node is encountered that represents a property. This
     * method will add an entry representative of the given dom node to a given
     * Properties object
     * 
     * @param node
     *            This is the dom node which represents a property
     * @param properties
     *            This is the Properties object to which the given property
     *            should be added.
     * @throws Exception
     *             This method throws an exception if the property has been
     *             defined with an incorrect type.
     */
    private void parseProperties(Node node, Properties properties)
            throws BallotParserException {
        NamedNodeMap nodeAttributes = node.getAttributes();
        String key = nodeAttributes.getNamedItem( "name" ).getNodeValue();
        String value = nodeAttributes.getNamedItem( "value" ).getNodeValue();
        String type = nodeAttributes.getNamedItem( "type" ).getNodeValue();
        try {
            properties.add( key, value, type );
        }
        catch (UnknownTypeException e) {
            throw new BallotParserException( "While parsing the property "
                    + key + " of type " + type + " and value " + value
                    + ", the parser encountered an error: " + e.getMessage(), e );
        }
        catch (UnknownFormatException e) {
            throw new BallotParserException( "While parsing the property "
                    + key + " of type " + type + " and value " + value
                    + ", the parser encountered an error: " + e.getMessage(), e );
        }
    }

    /**
     * Given an XML node whose type is "ListProperty", add all its children to
     * the given Properties instance.
     * 
     * @param node
     *            This is the list property node.
     * @param properties
     *            Add the children of the given node to this properties
     *            instance.
     * @throws BallotParserException
     *             If the XML is not formatted correctly, this method will
     *             throw.
     */
    private void parseListProperties(Node node, Properties properties)
            throws BallotParserException {
        NamedNodeMap nodeAttributes = node.getAttributes();
        String key = nodeAttributes.getNamedItem( "name" ).getNodeValue();
        String type = nodeAttributes.getNamedItem( "type" ).getNodeValue();

        NodeList children = node.getChildNodes();
        ArrayList<String> elts = new ArrayList<String>();
        for (int lcv = 0; lcv < children.getLength(); lcv++) {
            Node child = children.item( lcv );
            if (child.getNodeName().equals( "ListElement" )) {
                elts.add( child.getAttributes().getNamedItem( "value" )
                        .getNodeValue() );
            }
        }
        try {
            properties.add( key, elts, type );
        }
        catch (UnknownTypeException e) {
            throw new BallotParserException( "While parsing the property "
                    + key + " of type " + type + " and value " + elts
                    + ", the parser encountered an error: " + e.getMessage(), e );
        }
        catch (UnknownFormatException e) {
            throw new BallotParserException( "While parsing the property "
                    + key + " of type " + type + " and value " + elts
                    + ", the parser encountered an error: " + e.getMessage(), e );
        }
    }
}
