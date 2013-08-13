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

import java.util.Observable;
import java.util.Observer;

import sexpression.ASExpression;
import sexpression.StringExpression;
import votebox.middle.Event;
import votebox.middle.Properties;
import votebox.middle.driver.DeselectionException;
import votebox.middle.driver.UnknownUIDException;


//TODO: think about removing onselect.

/**
 * 
 * A SelectableCardElement is a CardElement that can be toggled and focused on.
 * For the purposes of the voting machine runtime, toggling can be thought of as
 * the voter's expression of preference. Focusing is strictly a gui capability.
 * The "focused" element simply is the element which the user is currently
 * looking at. The only reason this state is supported model side is because the
 * model needs to define an image to hand to the view for when the element is
 * focused. This is important, since the voting machine should do no rendering
 * work during runtime. The focused, state, however unlike the selected state,
 * has nothing to do with the model.< para>
 * 
 * In order to gain the focusing capability, this class must implement the
 * IFocusable interface. This class also extends CardElement, because the
 * SelectableCardElement is a special kind of ballot element -- one that can be
 * selected.< para>
 * 
 */

public final class SelectableCardElement {

	private Card _parentCard;

	private String _uniqueID;

	private Properties _properties;

	/**
	 * This event is raised when the element becomes selected.
	 * 
	 */
	private Event _selectedEvent = new Event();

	/**
	 * This event is raised when the element is deselected.
	 * 
	 */
	private Event _deselectedEvent = new Event();

	/**
	 * This field holds the state of the selectable card element.
	 */
	private boolean _selected = false;

	/**
	 * The public can add or remove this handler from any of the card element's
	 * events. This handler will simply call deselect on this element.
	 */
	private Observer _deselectHandler;

	public SelectableCardElement(String uid, Properties properties) {
		_uniqueID = uid;
		_properties = properties;
		_deselectHandler = makeDeselectHandler();
		registerCountEvents();
	}

	/**
	 * This method is used to initialize the DeselectDelegate. < summary>
	 * 
	 * @return This method returns the observer whose job is to deselect the
	 *         corresponding element in the view.
	 */
	private Observer makeDeselectHandler() {
		return new Observer() {

			public void update(Observable o, Object arg) {
				try {
					getParentCard().getParent().getViewAdapter().deselect(
							getUniqueID());
				} catch (UnknownUIDException e) {
					//We can't nicely pass exceptions while using Observer
					//  aren't checked exceptions nifty?
					//  anyway, just report and go one our way
					System.out.println("Error encounted in deselect handler: "+e.getMessage());
					e.printStackTrace(System.err);
				} catch (DeselectionException e) {
					//Likewise
					System.out.println("Error encounted in deselect handler: "+e.getMessage());
					e.printStackTrace(System.err);
				}
			}
		};
	}

	/**
	 * Call this method to register two observers (one to happen on deselection
	 * and one to happen on selection) These events insure that the count that
	 * the ballot that this SCE belongs to keep is up to date after each
	 * selection is made.
	 * 
	 */
	private void registerCountEvents() {
		_selectedEvent.addObserver(new Observer() {
			public void update(Observable arg0, Object arg1) {
				_parentCard.getParent().incrementSelections();
			}
		});

		_deselectedEvent.addObserver(new Observer() {
			public void update(Observable o, Object arg) {
				_parentCard.getParent().decrementSelections();
			}
		});
	}

	public Card getParentCard() {
		return _parentCard;
	}

	public String getUniqueID() {
		return _uniqueID;
	}

	public Properties getProperties() {
		return _properties;
	}

	public void setParent(Card card) {
		_parentCard = card;
	}

	/**
	 * The outside calls this method if they wish to attempt to select this card
	 * element.
	 * 
	 * @throws CardStrategyException
	 *             This method throws if the strategy runs into a problem.
	 */
	public boolean select() throws CardStrategyException {
		return getParentCard().select(this);
	}

	/**
	 * The outside calls this method if they wish to attempt to deselect this
	 * card element.
	 * 
	 * @throws CardStrategyException
	 *             This method throws if the strategy runs into a problem.
	 */
	public boolean deselect() throws CardStrategyException {
		return getParentCard().deselect(this);
	}

	/**
	 * The card strategy should call this method to change the state of the
	 * selectable card element.
	 * 
	 * @param value
	 */
	public void setSelected(boolean value) {
		if(value != _selected && value == true){
			_selected = true;
			_selectedEvent.notifyObservers();
		}
		if(value != _selected && value == false){
			_selected = false;
			_deselectedEvent.notifyObservers();
		}
	}

	/**
	 * This is the getter method for _deselectHandler
	 * 
	 * @return _deselectHandler
	 */
	public Observer getDeselectHandler() {
		return _deselectHandler;
	}

	public Event getSelectedEvent() {
		return _selectedEvent;
	}

	public Event getDeselectedEvent() {
		return _deselectedEvent;
	}

	/**
	 * Call this method to check the state of this element.
	 * 
	 * @return This method returns true if this element is currently selected,
	 *         or false if it is not.
	 */
	public boolean isSelected() {
		return _selected;
	}

	public ASExpression toASExpression() {
		return StringExpression.makeString(getUniqueID());
	}
}