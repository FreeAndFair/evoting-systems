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

package votebox.middle.view;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;

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
import votebox.middle.ballot.BallotParserException;
import votebox.middle.view.widget.Button;
import votebox.middle.view.widget.Label;
import votebox.middle.view.widget.ToggleButton;
import votebox.middle.view.widget.ToggleButtonGroup;


/**
 * This class encapsulates the layout XML parser. The layout xml stores view
 * information -- it defines a set of pages, each which defines a set of widgets
 * (label, button, togglebutton, etc.) which have been arranged on the page for
 * some purpose (display a candidate's name, display a "next page" button,
 * etc.). This class's job is translate this information into a Layout object.
 * This class might be better thought of as a Layout deserializer, but we have
 * avoided this term so as not to mislead the reader into thinking that we are
 * using java object serialization.<br>
 * <br>
 * To deserialize a Layout object, this class first uses java's xerces wrapper
 * to parse a given layout xml file into a w3c dom tree. This dom tree is first
 * validated with our schema and then interpreted recursively from the top down.<br>
 * <br>
 * It is important to note that for any given ballot package there are multiple
 * layout files. Each layout file is representative of one (size, language)
 * tuple. The layout parser will need to know which layout file needs to be
 * parsed -- when you ask for a layout, you need to tell the parser which size
 * and language you desire.
 * 
 * @author derrley
 * 
 */
public class LayoutParser {

    private HashMap<String, LinkedList<IDrawable>> _drawables;

    /**
     * This is the core method for the layout parser. Call this method to
     * translate a layout xml file to a dom tree (as an intermediate
     * representation), then, primarily, to a ballot object.
     * 
     * @param vars
     *            This method needs to know where to look for xml files and
     *            media. It gets this information from this parameter
     * @param size
     *            The parser needs to know which layout xml file to read. This
     *            parameter specifies the size index.
     * @param lang
     *            The parser needs to know which layout xml file to read. This
     *            paramter specifies the language.
     * @return This method returns the Layout object which represents the parsed
     *         and translated layout xml file.
     * @throws Exception
     *             This method throws if the xml file or schema could not be
     *             read, if the schema did not validate, or upon further testing
     *             of our own, the layout content is not valid.
     */
    public Layout getLayout(IBallotVars vars, int size, String lang)
            throws LayoutParserException {
        _drawables = new HashMap<String, LinkedList<IDrawable>>();

        // document = new Document(); // sometimes patterns suck
        Document document;
        try {
            document = DocumentBuilderFactory.newInstance()
                    .newDocumentBuilder().newDocument();
        }
        catch (ParserConfigurationException e) {
            throw new LayoutParserException(
                    "Internal Error. Could not get a new XML 'Document'.", e );
        }

        // parse layout xml -> dom tree.
        try {
            TransformerFactory.newInstance().newTransformer().transform(
                new StreamSource( new File( vars.getLayoutFile() + "_" + size
                        + "_" + lang + ".xml" ) ), new DOMResult( document ) );
        }
        catch (TransformerConfigurationException e) {
            throw new LayoutParserException(
                    "Internal Error. Could not get a new 'transformer'.", e );
        }
        catch (TransformerException e) {
            throw new LayoutParserException(
                    "The XML you have given for size "
                            + size
                            + ", language "
                            + lang
                            + " is unparseable. The XML is probably not formed correctly.",
                    e );
        }

        // validate the dom tree against our schema
        try {
            SchemaFactory.newInstance( XMLConstants.W3C_XML_SCHEMA_NS_URI )
                    .newSchema( vars.getLayoutSchema() ).newValidator()
                    .validate( new DOMSource( document ) );
        }
        catch (SAXException e) {
            throw new LayoutParserException(
                    "Could not validate the XML against the schema.", e );
        }
        catch (IOException e) {
            throw new LayoutParserException(
                    "Internal Error. The schema against which the XML is validated could not be loaded.",
                    e );
        }

        // translate dom tree -> Layout object.
        return parseLayout( document.getElementsByTagName( "Layout" ).item( 0 ) );
    }

    /**
     * This method interprets a given dom node as being of the layout type. This
     * method will convert the given dom node to a Layout object
     * 
     * @param node
     *            This is the dom node that is interpreted as being of type
     *            layout *
     * @return This method returns the newly constructed Layout object.
     */
    private Layout parseLayout(Node node) throws LayoutParserException {
        NodeList children = node.getChildNodes();
        ArrayList<RenderPage> pages = new ArrayList<RenderPage>();
        Properties properties = new Properties();

        // Children can either be properties or pages
        for (int lcv = 0; lcv < children.getLength(); lcv++) {
            Node child = children.item( lcv );

            if (child.getNodeName().equals( "Property" ))
                parseProperties( child, properties );
            else if (child.getNodeName().equals( "ListProperty" ))
                parseListProperties( child, properties );
            else if (child.getNodeName().equals( "Page" ))
                pages.add( parsePage( child ) );
            else if (child.getNodeName().equals( "#text" ))
                ;// Do nothing
            else
                throw new LayoutParserException(
                        "I don't recognize " + child.getNodeName()
                                + " as being a Property or Page.", null );
        }

        return new Layout( properties, pages, _drawables );
    }

    /**
     * This method is a helper to parseLayout. This method converts a dom node
     * into a RenderPage object.
     * 
     * @param node
     *            This is the page node which is interpreted as a page.
     * @return This method returns the RenderPage object that represents the
     *         given dom page.
     */
    private RenderPage parsePage(Node node) throws LayoutParserException {
        NodeList children = node.getChildNodes();
        ArrayList<IDrawable> drawables = new ArrayList<IDrawable>();
        Properties properties = new Properties();

        for (int lcv = 0; lcv < children.getLength(); lcv++) {
            Node child = children.item( lcv );

            if (child.getNodeName().equals( "ToggleButtonGroup" ))
                parseToggleGroup( drawables, child );
            else if (child.getNodeName().equals( "Button" )
                    || child.getNodeName().equals( "Label" )) {
                drawables.add( parseDrawable( child, null ) );
            }
            else if (child.getNodeName().equals( "#text" ))
                ; // Do Nothing
            else if (child.getNodeName().equals( "Property" ))
                parseProperties( child, properties );
            else if (child.getNodeName().equals( "ListProperty" ))
                parseListProperties( child, properties );
            else
                throw new LayoutParserException( "I dont recognize "
                        + child.getNodeName()
                        + " as being a ToggleButtonGroup, Button, or Label",
                        null );

        }

        RenderPage rp = new RenderPage( drawables, properties );
        rp.setNavigation( _drawables );
        rp.setBackgroundImage( _drawables );
        return rp;
    }

    /**
     * This method is a helper to parsePage. This method converts a dom node
     * into a ToggleButtonGroup.
     * 
     * @param list
     *            This method will add all children toggle buttons to this list
     *            of togglebuttons, as membership in a group does not place
     *            toggle buttons as members of the layout. Groups only serve the
     *            purpose of implenting select/deselect strategies.
     * @param node
     *            This is the node that is interpreted as the toggle button
     *            group.
     */
    private void parseToggleGroup(ArrayList<IDrawable> list, Node node)
            throws LayoutParserException {
        NodeList children = node.getChildNodes();
        Properties properties = new Properties();
        ToggleButtonGroup group = new ToggleButtonGroup( properties );

        for (int lcv = 0; lcv < children.getLength(); lcv++) {
            Node child = children.item( lcv );

            if (child.getNodeName().equals( "Property" ))
                parseProperties( child, properties );
            else if (child.getNodeName().equals( "ListProperty" ))
                parseListProperties( child, properties );
            else if (child.getNodeName().equals( "ToggleButton" )) {
                ToggleButton button = (ToggleButton) parseDrawable( child,
                    group );
                group.getButtons().add( button );
                list.add( button );
            }
            else if (child.getNodeName().equals( "#text" ))
                ; // Do nothing
            else
                throw new LayoutParserException( "I dont recognize "
                        + child.getNodeName()
                        + " as a property or toggle button.", null );
        }
    }

    /**
     * This method is a helper to parseToggleGroup and to parsePage. This method
     * converts a dom node into an IDrawable.
     * 
     * @param node
     *            This is the node which will be interpreted as an IDrawable.
     * @param group
     *            This is the group that this node needs to belong to. Pass null
     *            here if this drawable does not belong to a group (or if a
     *            group makes no sense -- IE label, etc.)
     * @return This method returns the newly constructed drawable which
     *         represents the given dom node.
     * @throws Exception
     *             This method throws if its helpers throw or if one of its
     *             children is not a property.
     */
    private IDrawable parseDrawable(Node node, ToggleButtonGroup group)
            throws LayoutParserException {
        NamedNodeMap nodeAttributes = node.getAttributes();
        NodeList children = node.getChildNodes();

        // Extract the drawable's unique id.
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
                throw new LayoutParserException( "I dont recgonize "
                        + child.getNodeName() + " as a property.", null );
        }

        // Create the new drawable
        IDrawable drawable = null;
        if (node.getNodeName().equals( "Label" )) {
            drawable = new Label( uniqueID, properties );
        }
        else if (node.getNodeName().equals( "Button" )) {
            drawable = new Button( uniqueID, properties );
        }
        else {
            drawable = new ToggleButton( group, uniqueID, properties );
        }

        // Extract the drawable's position
        drawable.setX( Integer.parseInt( nodeAttributes.getNamedItem( "x" )
                .getNodeValue() ) );
        drawable.setY( Integer.parseInt( nodeAttributes.getNamedItem( "y" )
                .getNodeValue() ) );

        // Add this drawable to the hash table.
        if (_drawables.containsKey( uniqueID ))
            _drawables.get( uniqueID ).add( 0, drawable );
        else {
            LinkedList<IDrawable> l = new LinkedList<IDrawable>();
            l.add( drawable );
            _drawables.put( uniqueID, l );
        }

        return drawable;
    }

    /**
     * This is a helper method to parseLayout and parseElement. It is called
     * when a dom node is encountered that represents a property. This method
     * will add an entry representative of the given dom node to a given
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
            throws LayoutParserException {
        NamedNodeMap nodeAttributes = node.getAttributes();
        String key = nodeAttributes.getNamedItem( "name" ).getNodeValue();
        String value = nodeAttributes.getNamedItem( "value" ).getNodeValue();
        String type = nodeAttributes.getNamedItem( "type" ).getNodeValue();
        try {
            properties.add( key, value, type );
        }
        catch (UnknownTypeException e) {
            throw new LayoutParserException(
                    "There was an error while parsing the property " + key
                            + " with type " + type + " and value " + value
                            + e.getMessage(), e );
        }
        catch (UnknownFormatException e) {
            throw new LayoutParserException(
                    "There was an error while parsing the property " + key
                            + " with type " + type + " and value " + value
                            + e.getMessage(), e );
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
            throws LayoutParserException {
        NamedNodeMap nodeAttributes = node.getAttributes();
        String key = nodeAttributes.getNamedItem( "name" ).getNodeValue();
        String type = nodeAttributes.getNamedItem( "type" ).getNodeValue();

        NodeList children = node.getChildNodes();
        ArrayList<String> elts = new ArrayList<String>();
        for (int lcv = 0; lcv < children.getLength(); lcv++) {
            Node child = children.item( lcv );
            elts.add( child.getAttributes().getNamedItem( "value" )
                    .getNodeValue() );
        }
        try {
            properties.add( key, elts, type );
        }
        catch (UnknownTypeException e) {
            throw new LayoutParserException( "While parsing the property "
                    + key + " of type " + type + " and value " + elts
                    + ", the parser encountered an error: " + e.getMessage(), e );
        }
        catch (UnknownFormatException e) {
            throw new LayoutParserException( "While parsing the property "
                    + key + " of type " + type + " and value " + elts
                    + ", the parser encountered an error: " + e.getMessage(), e );
        }
    }
}
