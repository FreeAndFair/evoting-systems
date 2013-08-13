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

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import sexpression.ASExpression;
import sexpression.ListExpression;
import votebox.middle.Properties;
import votebox.middle.driver.DeselectionException;
import votebox.middle.driver.IAdapter;
import votebox.middle.driver.SelectionException;
import votebox.middle.driver.UnknownUIDException;

/**
 * 
 * Ballots can only be created by instances of this delegate, which are handed
 * out to known
 * 
 * The Ballot Class represents the runtime version of the ballot. This means
 * that a Ballot contains both Cards and Properties. The Cards define the
 * information that the user will be presented with and the Properties determine
 * how that information will be presented.
 * 
 */
public final class Ballot {

    public static final ASExpression BALLOT_PATTERN = ASExpression
            .make("#list:(#string #any)");
    
    /**
	 * These are the cards that this ballot contains.
	 */
    private List<Card> _cards;
    
	/**
	 * These are the properties that were defined in the ballot's XML file.
	 */
    private Properties _properties;
    
    private HashMap<String, SelectableCardElement> _elements;
    private IAdapter _adapter = null;

    /**
     * This field holds how many selections have been made in the ballot.
     */
    private int _numSelections = 0;
    
    /**
     * List of the lists of race-ids that make up each race in the ballot.
     */
    private List<List<String>> _raceGroups = null;

    /**
     * This is Ballot's public constructor.
     * 
     * @param cards
     *            These are the cards that make up this ballot
     * @param properties
     *            These are the properties that were defined in the ballot's XML
     *            file.
     * @param elements
     *            These are the elements that make up this ballot. This is a
     *            dictionary mapping a unique id to its corresponding card
     *            element for every card element contained in this ballot
     * @param raceGroups
     * 	          For every race, the race-ids that make it up.  This is equivalent
     *            to a list of lists such that each sub list may only have one
     *            child element selected in a valid ballot at any time.
     */
    public Ballot(List<Card> cards, Properties properties,
            HashMap<String, SelectableCardElement> elements,
            List<List<String>> raceGroups) {
        _cards = cards;
        _properties = properties;
        _elements = elements;
        _raceGroups = raceGroups;

        // 1) Set the parent pointer for each card back to this ballot
        // 2) Set the strategy of each card that this ballot contains
        for (Card c : _cards) {
            c.setParent(this);
            c.setStrategy();
        }
    }

    /**
     * @return the Cards that make up this ballot
     */
    public List<Card> getCards() {
        return _cards;
    }

    /**
     * @return Properties associated with this ballot
     */
    public Properties getProperties() {
        return _properties;
    }

    /**
     * @return this ballot's view adapter
     */
    public IAdapter getViewAdapter() {
        return _adapter;
    }

    /**
     * Sets this ballot's view adapter
     * @param value - new IAdapter to use
     */
    public void setViewAdapter(IAdapter value) {
        _adapter = value;
    }

    /**
     * Call this method to get the number of selections that have been made on
     * this ballot. This does not include selections of "none.' This only
     * includes non-empty selections present at the time of the method call. *
     * 
     * @return _numSelections
     */
    public int getNumSelections() {
        return _numSelections;
    }

    /**
     * Call this method to decrement the count of the number of selections that
     * the ballot thinks have been made. This method should only be called by
     * SelectableCardElement.
     */
    public void incrementSelections() {
        _numSelections++;
    }

    /**
     * Call this method to decrement the count of the number of selections that
     * the ballot thinks have been made. This method should only be called by
     * SelectableCardElement.
     */
    public void decrementSelections() {
        _numSelections--;
    }

    /**
     * Selects an element based on its UID.
     * 
     * @param uniqueID - UID in question
     * @return the result of SelectableCardElement.select(), on the found element
     * @throws UnknownUIDException - if element with uniqueID could not be found
     * @throws SelectionException - if selection failed
     */
    public boolean select(String uniqueID) throws UnknownUIDException,
            SelectionException {
        SelectableCardElement ce = _elements.get(uniqueID);
        if (ce == null)
            throw new UnknownUIDException(uniqueID);

        try {
            return ce.select();
        } catch (CardStrategyException e) {
            throw new SelectionException("Problem selecting " + uniqueID + ":"
                    + e.getMessage(), e);
        }
    }

    /**
     * Deselects an element based on its UID.
     * 
     * @param uniqueID - UID in question
     * @return the result of SelectableCardElement.deselect(), on the found element
     * @throws UnknownUIDException - if element with uniqueID could not be found
     * @throws SelectionException - if deselection failed
     */
    public boolean deselect(String uniqueID) throws UnknownUIDException,
            DeselectionException {
        SelectableCardElement ce = _elements.get(uniqueID);
        if (ce == null)
            throw new UnknownUIDException(uniqueID);

        try {
            return ce.deselect();
        } catch (CardStrategyException e) {
            throw new DeselectionException("Problem deselecting " + uniqueID
                    + ":" + e.getMessage(), e);
        }
    }

    /**
     * @param uid - UID of element to interogate
     * @return true, if selected and false otherwise
     * @throws UnknownUIDException - if the element could not be found
     */
    public boolean isSelected(String uid) throws UnknownUIDException {
        SelectableCardElement ce = _elements.get(uid);
        if (ce == null)
            throw new UnknownUIDException(uid);

        return ce.isSelected();
    }

    /**
     * @param uid - UID to attempt to find
     * @return true if an element with the UID was found, false otherwise
     */
    public boolean exists(String uid) {
        // Check if it is an element.
        if (_elements.containsKey(uid))
            return true;

        // Check if it is a card.
        for (Card c : this.getCards())
            if (c.getUniqueID().equals(uid))
                return true;

        return false;
    }

    /**
     * @param UID - UID of element to find
     * @return true, if UID is a Card
     * @throws UnknownUIDException - if an Element with UID could not be found.
     */
    public boolean isCard(String UID) throws UnknownUIDException {
        // Check that it exists anywhere.
        if (!exists(UID))
            throw new UnknownUIDException(UID);

        // Check if it is an element.
        if (_elements.containsKey(UID))
            return false;

        return true;
    }

    /**
     * Returns the UID of the selected element in the card identified by UID.
     * 
     * @param UID - UID of card to interogate
     * @return the UID of that card's selected element, if any
     * @throws NonCardException - if UID does not map to a Card
     * @throws UnknownUIDException - if UID does not exist
     * @throws CardException - If more than one element is selected on the given Card.
     */
    public String selectedElement(String UID) throws NonCardException,
            UnknownUIDException, CardException {
        // First, check for the correct behavior. Get the selected
        // element from the card.
        for (Card c : getCards())
            if (c.getUniqueID().equals(UID))
                return c.getSelectedElement();

        // If control gets here, something is wrong. The UID either
        // doesn't exist or isn't a card.
        if (!isCard(UID))
            throw new NonCardException(UID);

        throw new RuntimeException("Control should never get here.");
    }

    /**
     * @return the SExpression representation of this Ballot.
     */
    public ASExpression toASExpression() {
        ArrayList<ASExpression> cardList = new ArrayList<ASExpression>();
        for (Card card : _cards)
            cardList.add(card.toASExpression());
        return new ListExpression(cardList);
    }

    /**
     * New as of 1/28/2008: Cast ballot representation.
     * 
     * @return This method returns the cast ballot representation, ready for
     *         encryption. Each selectable in the ballot is represented by the
     *         pair (uid, counter), where "counter" is either BigInteger.ZERO or
     *         BigInteger.ONE (in byte[] format, converted to an s-expression
     *         byte string).
     */
    public ListExpression getCastBallot() {
        ArrayList<ASExpression> pairs = new ArrayList<ASExpression>();
        for (Card card : _cards)
            pairs.addAll(card.getCastBallot());
        return new ListExpression(pairs);
    }
    
    /**
     * Accessor for the race group parameter passed at construction.
     * Refer there for more discussion.
     * 
     * @return the race groups of this ballots
     * @see {@link #Ballot(List, Properties, HashMap, List)}
     */
    public List<List<String>> getRaceGroups(){
    	return _raceGroups;
    }
}
