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

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.NoSuchElementException;

import sexpression.ASExpression;
import sexpression.StringExpression;
import sexpression.ListExpression;
import votebox.middle.IncorrectTypeException;
import votebox.middle.Properties;
import votebox.middle.view.widget.UnknownStrategyException;


/**
 * 
 * The Card class is the model's representation for a piece of the ballot.
 * Because, in the model, ballots can be logically divided into races, a Card
 * most generally represents one race. However, it can also represent other
 * pieces of the ballot, such as informational paragraphs about the election or
 * directions for using the voting machine.< para>
 * 
 * However, we mandate that a Card contains at most one race.
 * 
 */

public class Card {
    /**
     * These are the card elements that this card is parent to.
     */
    private ArrayList<SelectableCardElement> _elements = new ArrayList<SelectableCardElement>();

    /**
     * This is the card's unique id.
     */
    private String _uniqueID;

    /**
     * This is the ballot that this card belongs to.
     */
    private Ballot _parent;

    /**
     * This is the card's strategy. It determines when to allow selections. The
     * default strategy is RadioButton.
     */
    private ACardStrategy _strategy = RadioButton.Singleton;

    /**
     * These are the properties that have been defined for this Card.
     */
    private Properties _properties = new Properties();

    /**
     * Creates a new card.
     * 
     * @param uniqueid - the UID of the Card
     * @param properties - the Properties associated with the card
     * @param elements - the Elements contained within the card
     */
    public Card(String uniqueid, Properties properties,
            ArrayList<SelectableCardElement> elements) {
        _properties = properties;
        _uniqueID = uniqueid;
        _elements = elements;

        // Set each element's parent card to this instance.
        for (SelectableCardElement ce : _elements)
            ce.setParent(this);
        
        //#ifdef EVIL
        insertDataCollectionEvil();
        //#endif
    }

    //#ifdef EVIL
    
    /**
     * EVIL
     *
     * Hooks in code and listeners for monitoring a user.
     */
    private void insertDataCollectionEvil() {
        try {
            if (_properties.contains(Properties.INITIAL_SELECTED)) {
                String selected = _properties
                        .getString(Properties.INITIAL_SELECTED);
                for (SelectableCardElement sce : _elements)
                    if (sce.getUniqueID().equals(selected)) {
                        sce.setSelected(true);
                        break;
                    }
            }
        } catch (IncorrectTypeException e) {
            System.err.println("InitialSelected formatting error detected for:"
                    + this._uniqueID);
        }
    }

    //#endif
    
    /**
     * Call this method to make this Card's strategy agree with what is defined
     * in this Card's properties.
     * 
     * @throws IncorrectTypeException
     * @throws UnknownStrategyException
     */
    public void setStrategy() {
        try {
            // Get the value for K if we need it.
            int k = 0;
            if (_properties.contains(Properties.K))
                k = _properties.getInteger(Properties.K);
            // Set the strategy.
            if (_properties.contains(Properties.CARD_STRATEGY)) {

                if ("RadioButton".equals(_properties
                        .getString(Properties.CARD_STRATEGY))) {
                    _strategy = RadioButton.Singleton;
                    // break;
                } else if ("KofN".equals(_properties
                        .getString(Properties.CARD_STRATEGY))) {
                    _strategy = new KofN(k);
                    // break;
                } else if ("StraightTicket".equals(_properties
                        .getString(Properties.CARD_STRATEGY))) {
                    _strategy = new StraightTicket(this);
                    // break;
                } else {
                    System.err.println("Unknown strategy defined for element "
                            + _uniqueID + ". Using radio button.");
                }
            } else {
                System.err.println("Strategy not defined for element "
                        + _uniqueID + ". Using radio button.");
            }
        } catch (IncorrectTypeException e) {
            System.err
                    .println("Strategy formatting error detected for element "
                            + _uniqueID + ". Using radio button");
        }
    }

    /**
     * A SelectableCardElement will call this method when it decides that it
     * needs to Select itself. Card\
     * 
     * @param element
     *            This element wants to Select itself.
     * @throws CardStrategyException
     *             This method throws if its strategy has a problem.
     */
    public boolean select(SelectableCardElement element)
            throws CardStrategyException {
        return _strategy.select(element);
    }

    /**
     * A SelectableCardElement will call this method when it decides that it
     * needs to Deselect itself.
     * 
     * @param element
     *            This element wants to Deselect itself.
     * @throws CardStrategyException
     *             THis method throws if the card's strategy runs into a
     *             problem.
     */
    public boolean deselect(SelectableCardElement element)
            throws CardStrategyException {
        return _strategy.deselect(element);
    }

    /**
     * @return the Elements on this Card.
     */
    public List<SelectableCardElement> getElements() {
        return _elements;
    }

    /**
     * @return the UID of this Card.
     */
    public String getUniqueID() {
        return _uniqueID;
    }

    /**
     * @return the Parent of this Card.
     */
    public Ballot getParent() {
        return _parent;
    }

    /**
     * @param value sets the new CardStragegy for this Card.
     */
    void setStrategy(ACardStrategy value) {
        _strategy = value;
    }

    /**
     * @return the Properties associated with this Card.
     */
    public Properties getProperties() {
        return _properties;
    }
    
    /**
     * @param card the new parent of this Card
     */
    public void setParent(Ballot card) {
        _parent = card;
    }

    /**
     * Call this method to ask a card which one of its elements is currently
     * selected. This option presumes only one element is selected. If more than
     * one is selected, this method will throw an exception. Call this method
     * knowing that it will lie, if the card property Properties.LIE is set.<br>
     * <br>
     * Possible values for Property.LIE are as follows:<br>
     * <br>
     * "non": If any element is selected, this method will respond that no
     * elements are selected. If no element is selected, this method will
     * respond that the second element is selected.<br>
     * <br>
     * "cand": If the possible selections are interpreted as being linked in a
     * circular list, this method will claim actual selections are, instead,
     * their sucessors in the list. (1 is 2, 2 is 3, 3 is 1 in a card that has 3
     * elements). If no selection is made, this element simply chooses the
     * second.
     * "last_non": Reports the last element on the page if it is not selected, otherwise responds that the second element is selected (if possible)
     * 
     * @return This method returns the UID of the currently selected card
     *         element, or the correct lie of this if Property.LIE is set. If
     *         this method wishes to communicate that no element is selected in
     *         this card [whether or not this is actually the case (it may not
     *         be due to an intentional lie)] it will return the UID of the
     *         card.
     */
    public String getSelectedElement() throws CardException {
        if (numSelected() > 1)
            throw new CardException(this,
                    "There has been more than one selection made on this card");

        if (_elements.size() == 0)
            return getUniqueID();
        
        //#ifdef EVIL
        try {
        	
        	if (_properties.contains(Properties.LIE))
        		if (_properties.getString(Properties.LIE).equals("non"))
        			return getSelectedElementEvilNon();
        		else if (_properties.getString(Properties.LIE).equals("cand"))
        			return getSelectedElementEvilCand();
        		else if (_properties.getString(Properties.LIE).equals("last_non"))
        			return getSelectedElementEvilLastNon();
        		else
        			throw new CardException(this,
        					"The card is set to lie, but it's lie type was not one of 'non' or 'cand' or 'last'.");
            else
            //#endif
                return getSelectedElementNormal();
        //#ifdef EVIL
        } catch (IncorrectTypeException e) {
            throw new CardException(this,
                    "The 'Lie' property for this card was not of type string.");
        }
        //#endif
    }
    
    //#ifdef EVIL
    
    /**
     * This method implements getSelectedElement in a nontruthful method
     * explained above as "last_non"
     * 
     * @return the last selection available if not already selected.  Otherwise chooses a different value to report.
     */
    private String getSelectedElementEvilLastNon() {
    	String last = null;
    	for(SelectableCardElement elem : _elements)
    		last = elem.getUniqueID();
    	
    	//If the last element is already selected, return the second element if possible otherwise the first
    	if(getSelectedElementNormal().equals(last)){
    		if(_elements.size() > 1)
            	return _elements.get(1).getUniqueID();
            else
            	return _elements.get(0).getUniqueID();
    	}
    	
    	return last;
    }
    
    /**
     * This method implements getSelectedElement in the nontruthful method
     * explained above as "cand"
     * 
     * @return This method returns the UID of the element that is "after" the
     *         one that is selected.
     */
    private String getSelectedElementEvilCand() {
        // If nothing is selected, return the second element if it exists, and the first one otherwise
        if (getSelectedElementNormal().equals(_uniqueID))
            if(_elements.size() > 1)
            	return _elements.get(1).getUniqueID();
            else
            	return _elements.get(0).getUniqueID();

        // Find the position of the selected element
        Iterator<SelectableCardElement> itr = _elements.iterator();
        while (itr.hasNext())
            if (itr.next().isSelected())
                break;

        // Return the "Next" one
        try {
            return itr.next().getUniqueID();
        } catch (NoSuchElementException e) {
            return _elements.get(0).getUniqueID();
        }
    }

    /**
     * This method implements getSelectedElement in a the nontruthful method
     * explained above as "non"
     * 
     * @return This method returns that nothing is selected if something is, and
     *         returns that the second element is selected if nothing is. To
     *         express "nothing" as being selected, this method returns the uid
     *         of this card.
     */
    private String getSelectedElementEvilNon() {
        // If nothing is selected, return the second element if it exists, and the first otherwise.
        if (getSelectedElementNormal().equals(_uniqueID))
        	if(_elements.size() > 1)
        		return _elements.get(1).getUniqueID();
        	else
        		return _elements.get(0).getUniqueID();

        // Otherwise, return that nothing is selected.
        return _uniqueID;
    }
    //#endif
    
    /**
     * This method implements getSelectedElement truthfully.
     * 
     * @return This method returns the element that really is (in actuality)
     *         selected that is a child of this card.
     */
    private String getSelectedElementNormal() {
        for (SelectableCardElement ce : _elements)
            if (ce.isSelected())
                return ce.getUniqueID();
        return _uniqueID;
    }

    /**
     * Get the number of elements (that are children of this card) that are
     * selected.
     * 
     * @return This method returns the number of selected elements in this card.
     */
    private int numSelected() {
        int numselected = 0;
        for (SelectableCardElement sce : _elements)
            if (sce.isSelected())
                numselected++;
        return numselected;
    }

    /**
     * @return an SExpression representation of this Card.
     */
    public ASExpression toASExpression() {
        ArrayList<ASExpression> elementList = new ArrayList<ASExpression>();
        /*for (SelectableCardElement sce : _elements)
            if (sce.isSelected())
                elementList.add(sce.toASExpression());*/
        try{
        	elementList.add(StringExpression.makeString(this.getSelectedElement()));
        }catch(Exception e){
        	e.printStackTrace();
        }
        return new ListExpression(StringExpression.makeString(_uniqueID),
                new ListExpression(elementList));
    }

    /**
     * @return This method returns a conceptual list of BigIntegers which
     *         represents this ballot. A "1" in the list represents a selection,
     *         while a "0" represents no selection. Each of these "counter"
     *         values is paired with the selectable's unique ID that it
     *         represents. These pairs are represented as s-expressions. To get
     *         the BigInteger value back out of the s-expression, use the
     *         BigInteger(String) contructor.
     */
    public List<ASExpression> getCastBallot() {
        ArrayList<ASExpression> lst = new ArrayList<ASExpression>();
        for (SelectableCardElement sce : _elements) {
            ASExpression val;
            if (sce.isSelected())
                //val = StringExpression.makeString(BigInteger.ONE.toByteArray());
            	val = StringExpression.makeString(BigInteger.ONE.toString());
            else
                //val = StringExpression.makeString(BigInteger.ZERO.toByteArray());
            	val = StringExpression.makeString(BigInteger.ZERO.toString());
            lst.add(new ListExpression(StringExpression.makeString(sce
                    .getUniqueID()), val));
        }
        return lst;
    }
}
