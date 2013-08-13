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

package votebox.middle;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

/**
 * The properties class is used to store, in the state of any ballot or layout
 * object, properties that are declared in the corresponding XML file. When
 * ballot or layout objects are parsed, any time a "Property" or "ListProperty"
 * tag is encountered, the mapping defined in the tag is stored in the instance
 * of this class that is held by parent ballot or layout object. This allows for
 * these properties to be easily checked at any time.
 */

public class Properties {

    /**
     * The value of this property tells you what the maximum size index is for
     * any given drawable
     */
    public static final String MAX_IMAGE_SIZE = "MaxImageSize";

    /**
     * The value of this property tells you what the initial size index should
     * be when the voting runtime launches.
     */
    public static final String START_IMAGE_SIZE = "StartImageSize";
    
    /**
     * The value of this property is the page number of the override cancel page.
     */
    public static final String OVERRIDE_CANCEL_PAGE = "OverrideCancelPage";
    
    /**
     * The value of this property is the page number of the override cast page.
     */
    public static final String OVERRIDE_CAST_PAGE = "OverrideCastPage";
    
    /**
     * The value of this property is the page number of the challenge respnse page.
     */
    public static final String RESPONSE_PAGE = "ResponsePage";

    /**
     * This property assigns party affiliation to a candidate.
     */
    public static final String PARTY = "Party";

    /**
     * Cards can have this property set to denote k in kofn in reference to KofN
     * voting, or voting in races where a certain number (k) of candidates can
     * be selected out of all the candidates in the race (n).
     */
    public static final String K = "K";

    /**
     * Set this property on a card to set the "strategy" that the card uses for
     * the behavior of CardElement selection and deselection.
     */
    public static final String CARD_STRATEGY = "CardStrategy";

    /**
     * Set this property on a button to set the "strategy" that the button
     * executes when it is selected. This property defines the behavior of the
     * button when it is selected.
     */
    public static final String BUTTON_STRATEGY = "ButtonStrategy";

    /**
     * Set this property on a ToggleButtonGroup to set the strategy that it uses
     * to dictate when ToggleButtons can select and deselect themselves.
     */
    public static final String TOGGLE_BUTTON_GROUP_STRATEGY = "ToggleButtonGroupStrategy";

    /**
     * Often, one will need to define a page number to correlate with another
     * assignment. For instance, the "go to page" button strategy will need a
     * page number to which it should "go."
     */
    public static final String PAGE_NUMBER = "PageNumber";
    
    /**
     * Defines the page number of the 'no selection' page corresponding to
     * the current page. For now, this has to be set manually in the output.
     */
    public static final String NO_SELECTION_PAGE_NUMBER = "NoSelectionPageNumber";
    
    /**
     * Specifies the UID of the containing ('parent') card.
     */
    public static final String PARENT_CARD = "ParentCard";

    /**
     * Set this property to name an element in the layout or in the ballot.
     */
    public static final String UID = "UID";

    /**
     * Set this property on a ballot to enable a specific language.
     */
    public static final String LANGUAGES = "Languages";

    /**
     * Set this property on a toggle button to choose which language is
     * selected.
     */
    public static final String LANGUAGE = "Language";

    /**
     * This property references the UID of the element that is laid out above
     * this element.
     */
    public static final String UP = "Up";

    /**
     * This property references the UID of the element that is laid out below
     * this element.
     */
    public static final String DOWN = "Down";

    /**
     * This property references the UID of the element that is laid out to the
     * left of this element.
     */
    public static final String LEFT = "Left";

    /**
     * This property references the UID of the element that is laid out to the
     * right of this element.
     */
    public static final String RIGHT = "Right";

    /**
     * This property references the UID of the element that is laid out "after"
     * this element.
     */
    public static final String NEXT = "Next";

    /**
     * This property references the uid of the lement that is laid out "before"
     * this element.
     */
    public static final String PREVIOUS = "Previous";

    /**
     * This is a property which can be defined on a page, telling the page which
     * label to use as a background image.
     */
    public static final String BACKGROUND_LABEL = "BackgroundLabel";

    /**
     * Set this property on a card to make an element be selected initially
     * (before a voter has touched it).
     */
    public static final String INITIAL_SELECTED = "InitialSelected";

    /**
     * Set this property on a card to either "non" or "cand" to enable lying and
     * to set which type of lying should be done.
     */
    public static final String LIE = "Lie";

    /**
     * Set this property to a list of race-ids to indicate the group of race-ids that compose the race on this card.
     * In the event that a race spans multiple cards, the FIRST card should contain this property
     * and it should be omitted on all subsequent cards in the race.
     */
    public static final String RACE_GROUP = "RaceGroup";
    
    /**
     * Here, we hold the actual property mappings.
     */
    private HashMap<String, Object> _properties = new HashMap<String, Object>();

    /**
     * This method adds a key and value to the properties dictionary. The key
     * must be of the type which is defined in the "type" attribute of the
     * property that is being added.
     * 
     * @param key
     *            Add this key to the dictionary
     * @param value
     *            Set this value for key
     * @param type
     *            This is value's type. It must be one of
     *            {"Integer","Boolean","String"}
     * @throws UnknownTypeException
     *             This method throws if type is not one of
     *             {"Integer","Boolean","String"}
     * @throws UnknownFormatException
     *             This method throws if value cannot be decoded, given that its
     *             type is the type parameter.
     */
    public void add(String key, String value, String type)
            throws UnknownTypeException, UnknownFormatException {
        if (type.equals( "Integer" )) {
            try {
                _properties.put( key, Integer.parseInt( value ) );
            }
            catch (NumberFormatException e) {
                throw new UnknownFormatException( type, value );
            }
        }
        else if (type.equals( "Boolean" )) {
            // Boolean.parseBoolean allows any string but "true" to be false.
            // This is not good enough. We want to allow only the strings "true"
            // and "false".
            if (value.equals( "false" ))
                _properties.put( key, Boolean.FALSE );
            else if (value.equals( "true" ))
                _properties.put( key, Boolean.TRUE );
            else
                throw new UnknownFormatException( type, value );
        }
        else if (type.equals( "String" )) {
            _properties.put( key, value );
        }
        else {
            throw new UnknownTypeException( type );
        }
    }

    /**
     * Add a list type property. A list type, rather than mapping a key to a
     * single value, maps it to a collection of values. These values must all be
     * of the same type.
     * 
     * @param key
     *            Map the given values to this key.
     * @param values
     *            Map these values.
     * @param type
     *            The values inside the collection are of this type (one of
     *            String, Integer). Note that boolean is not allowed.
     * @throws UnknownTypeException
     *             This method throws if type is not one of {"Integer","String"}
     * @throws UnknownFormatException
     *             This method throws if value cannot be decoded, given that its
     *             type is the type parameter.
     */
    public void add(String key, List<String> values, String type)
            throws UnknownTypeException, UnknownFormatException {
        if (values.isEmpty())
            throw new UnknownFormatException( type, "empty list" );
        if (type.equals( "Integer" )) {
            ArrayList<Integer> lst = new ArrayList<Integer>( values.size() );
            for (String value : values)
                try {
                    lst.add( Integer.parseInt( value ) );
                }
                catch (NumberFormatException e) {
                    throw new UnknownFormatException( type, value );
                }
            _properties.put( key, lst );
        }
        else if (type.equals( "String" )) {
            _properties.put( key, values );
        }
        else {
            throw new UnknownTypeException( type );
        }
    }

    /**
     * This method gets the value associated with a given key.
     * 
     * @param key
     *            This is the key for which a value will be returned.
     * @return This method returns the value associated with key if there is
     *         one, or null if there isn't. This method offers no guarentees
     *         about the type returned.
     * 
     * associated with the key
     */
    public Object getObject(String key) {
        return _properties.get( key );
    }

    /**
     * This method gets the value associated with a given key.
     * 
     * @param key
     *            This is the key for which a value will be returned.
     * @return This method returns the value associated with key if there is
     *         one, or null if there isn't. This method guarentees that the
     *         value returned is of type Integer.
     * @throws IncorrectTypeException
     *             This method throws if the object associated with key is not
     *             of the type Integer.
     */
    public Integer getInteger(String key) throws IncorrectTypeException {
        Object o = null;
        try {
            return (Integer) (o = _properties.get( key ));
        }
        catch (ClassCastException e) {
            throw new IncorrectTypeException( "Integer", o.getClass()
                    .getSimpleName() );
        }
    }

    /**
     * This method gets the value associated with a given key.
     * 
     * @param key
     *            This is the key for which a value will be returned.
     * @return This method returns the value associated with key if there is
     *         one, or null if there isn't. This method guarentees that the
     *         value returned is of type String.
     * @throws IncorrectTypeException
     *             This method throws if the object associated with key is not
     *             of the type String.
     */
    public String getString(String key) throws IncorrectTypeException {
        Object o = null;
        try {
            return (String) (o = _properties.get( key ));
        }
        catch (ClassCastException e) {
            throw new IncorrectTypeException( "String", o.getClass()
                    .getSimpleName() );
        }
    }

    /**
     * This method gets the value associated with a given key.
     * 
     * @param key
     *            This is the key for which a value will be returned.
     * @return This method returns the value associated with key if there is
     *         one, or null if there isn't. This method guarentees that the
     *         value returned is of type Boolean.
     * @throws IncorrectTypeException
     *             This method throws if the object associated with key is not
     *             of the type Boolean.
     */
    public Boolean getBoolean(String key) throws IncorrectTypeException {
        Object o = null;
        try {
            return (Boolean) (o = _properties.get( key ));
        }
        catch (ClassCastException e) {
            throw new IncorrectTypeException( "Boolean", o.getClass()
                    .getSimpleName() );
        }
    }

    /**
     * This method gets the value associated with a given key.
     * 
     * @param key
     *            This is the key for which a value will be returned.
     * @return This method returns the value associated with key if there is
     *         one, or null if there isn't. This method guarentees that the
     *         value returned is of type "List of Integers".
     * @throws IncorrectTypeException
     *             This method throws if the object associated with key is not
     *             of the type Boolean.
     */
    @SuppressWarnings("unchecked")
    public List<Integer> getIntegerList(String key)
            throws IncorrectTypeException {
        Object o = null;
        try {
            o = _properties.get( key );
            // Type erasure for the lose! Must check the contents of the list.
            List l = (List) o;
            if (!(l.get( 0 ) instanceof Integer))
                throw new IncorrectTypeException( "List<Integer>", "List<"
                        + l.get( 0 ).getClass().getSimpleName() + ">" );
            return (List<Integer>) l;
        }
        catch (ClassCastException e) {
            throw new IncorrectTypeException( "List", o.getClass()
                    .getSimpleName() );
        }
    }

    /**
     * This method gets the value associated with a given key.
     * 
     * @param key
     *            This is the key for which a value will be returned.
     * @return This method returns the value associated with key if there is
     *         one, or null if there isn't. This method guarentees that the
     *         value returned is of type "List of Integers".
     * @throws IncorrectTypeException
     *             This method throws if the object associated with key is not
     *             of the type "list of strings".
     */
    @SuppressWarnings("unchecked")
    public List<String> getStringList(String key) throws IncorrectTypeException {
        Object o = null;
        try {
            o = _properties.get( key );
            // Type erasure for the lose! Must check the contents of the list.
            List l = (List) o;
            if (!(l.get( 0 ) instanceof String))
                throw new IncorrectTypeException( "List<String>", "List<"
                        + l.get( 0 ).getClass().getSimpleName() + ">" );
            return (List<String>) l;
        }
        catch (ClassCastException e) {
            throw new IncorrectTypeException( "List", o.getClass()
                    .getSimpleName() );
        }
    }

    /**
     * Call this method to check if a given property has been set.
     * 
     * @param key
     *            This is the key for the given property.
     * @return This method returns true of the property has been set (has an
     *         assigned value) or false if it has not been.
     */
    public boolean contains(String key) {
        return _properties.containsKey( key );
    }

    /**
     * Call this method to get the number of properties that are mapped.
     * 
     * @return This method returns the number of properties that are mapped.
     */
    public int size() {
        return _properties.size();
    }
    
    /**
     * For debuging purposes, a meaningful toString().
     * @return String representation of this Properties object.
     */
    public String toString(){
    	return _properties.toString();
    }
}
