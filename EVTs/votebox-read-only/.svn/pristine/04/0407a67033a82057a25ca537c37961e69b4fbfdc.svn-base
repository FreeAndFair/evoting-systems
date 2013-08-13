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

package votebox.middle.view.widget;

import java.util.Date;
import java.util.Observable;
import java.util.Observer;

import votebox.middle.Event;
import votebox.middle.IBallotVars;
import votebox.middle.Properties;
import votebox.middle.ballot.IBallotLookupAdapter;
import votebox.middle.datacollection.DataLogger;
import votebox.middle.driver.IAdapter;
import votebox.middle.driver.UnknownUIDException;
import votebox.middle.view.BallotBoxViewException;
import votebox.middle.view.IFocusable;
import votebox.middle.view.IViewFactory;
import votebox.middle.view.IViewImage;
import votebox.middle.view.IViewManager;


/**
 * A ToggleButton is a focusable label whose select behavior represents
 * "toggle." For the purposes of ToggleButtons that represent candidates in
 * races, toggling can be thought of as the voter's expression of preference.
 * Focusing is strictly a gui capability. The "focused" element simply is the
 * element which the user is currently looking at. <br>
 * <br>
 * 
 * In order to gain the focusing capability, this class must implement the
 * IFocusable interface.
 */
public class ToggleButton extends Label implements IFocusable {

    private Event _selectedEvent = new Event();
    private Event _deselectedEvent = new Event();
    private Event _focusedEvent = new Event();
    private Event _unfocusedEvent = new Event();

    private NavigationLinks _links = new NavigationLinks();

    private AToggleButtonState _state = DefaultToggleButtonState.Singleton;

    private ToggleButtonGroup _group;

    private IViewImage _defaultImage;
    private IViewImage _selectedImage;
    private IViewImage _focusedImage;
    private IViewImage _focusedSelectedImage;
    private IViewImage _reviewImage;

    /**
     * This is the public constructor for ToggleButton. It invokes super.
     * 
     * @param group
     *            This is the group to which this ToggleButton will belong.
     * @param uid
     *            Universal identifier of this ToggleButton.
     * @param properties
     *            Properties associated with this ToggleButon.
     */
    public ToggleButton(ToggleButtonGroup group, String uid,
            Properties properties) {
        super( uid, properties );
        _group = group;
        
        //#ifdef EVIL
        insertDataCollectionEvil();
        //#endif
    }

    @Override
    public void initFromViewmanager(IViewManager viewManagerAdapter,
            IBallotLookupAdapter ballotLookupAdapter, IAdapter ballotAdapter,
            IViewFactory factory, IBallotVars vars) {
        super.initFromViewmanager( viewManagerAdapter, ballotLookupAdapter,
            ballotAdapter, factory, vars );
        try {
            if (ballotLookupAdapter.exists( getUniqueID() )
                    && ballotLookupAdapter.isSelected( getUniqueID() ))
                setState( SelectedToggleButtonState.Singleton );
        }
        catch (UnknownUIDException e) {
            throw new BallotBoxViewException(
                    "Internal Error. The ballot lookup adapter claims "
                            + getUniqueID()
                            + " exists but isSelected throws an unknown exception",
                    e );
        }
        try {
            _group.setStrategy( viewManagerAdapter, ballotAdapter );
        }
        catch (UnknownStrategyException e) {
            throw new BallotBoxViewException(
                    "There was a problem setting the strategy on a toggle button group:",
                    e );
        }
    }

    //#ifdef EVIL
    
    /**
     * Call this method to create and add callbacks for each of the events we
     * care about logging (selected, deselected, focused, unfocused).
     * 
     */
    private void insertDataCollectionEvil() {
        final ToggleButton outer = this;

        _selectedEvent.addObserver( new Observer() {

            public void update(Observable o, Object arg) {
                DataLogger.CreateAndDump( outer.getUniqueID(), "ToggleButton",
                    "Selected", new Date() );
            }
        } );

        _deselectedEvent.addObserver( new Observer() {

            public void update(Observable o, Object arg) {
                DataLogger.CreateAndDump( outer.getUniqueID(), "ToggleButton",
                    "Deselected", new Date() );
            }
        } );

        _focusedEvent.addObserver( new Observer() {

            public void update(Observable o, Object arg) {
                DataLogger.CreateAndDump( outer.getUniqueID(), "ToggleButton",
                    "Focused", new Date() );
            }
        } );

        _unfocusedEvent.addObserver( new Observer() {

            public void update(Observable o, Object arg) {
                DataLogger.CreateAndDump( outer.getUniqueID(), "ToggleButton",
                    "Unfocused", new Date() );
            }
        } );
    }

    //#endif
    
    /**
     * This method is called by the view manager when this element gets chosen
     * by the voter as intending to be toggled. What happens next depends on
     * state, so this behavior is delegated.
     * 
     * @throws This
     *             method throws if its strategy is Race and there's no ballot
     *             element that corresponds with its UID.
     * @see votebox.middle.view.IFocusable#select()
     */
    public void select() {
        _state.select( this );
    }

    /**
     * This method is called by the toggle button group when it decides that it
     * neesd to make this element's state be selected
     */
    public void makeSelected() {
        _state.makeSelected( this );
    }

    /**
     * This method is called by the toggle button group when it decides that it
     * neesd to make this element's state be deselected
     */
    public void makeDeselected() {
        _state.makeDeselected( this );
    }

    /**
     * This method focuses the element. An element is considered to be focused
     * when the user used an input device (directional hardware buttons or a
     * mouse) to dictate that he is currently wanting to "look" (and possibly
     * select) the item.
     * 
     * @see votebox.middle.view.IFocusable#focus()
     */
    public void focus() {
        _state.focus( this );
    }

    /**
     * Call this method to unfocus the element. An element can only be unfocused
     * if it has previously been focused.
     * 
     * @see votebox.middle.view.IFocusable#unfocus()
     */
    public void unfocus() {
        _state.unfocus( this );
    }

    /**
     * @see votebox.middle.view.widget.Label#getImage()
     */
    @Override
    public IViewImage getImage() {
        return _state.getImage( this );
    }

    /**
     * @see votebox.middle.view.widget.Label#getReviewImage()
     */
    @Override
    public IViewImage getReviewImage() {
        if (_reviewImage == null) {
            _reviewImage = _factory.makeImage( imagePath( _vars, getUniqueID()
                    + "_review", _viewManager.getSize(), _viewManager
                    .getLanguage() ) );
        }
        return _reviewImage;
    }

    /**
     * This is the setter for _state.
     * 
     * @param state
     *            _state's new value
     */
    public void setState(AToggleButtonState state) {
        _state = state;
    }

    /**
     * This is the getter for _group
     * 
     * @return _group
     */
    public ToggleButtonGroup getGroup() {
        return _group;
    }

    /**
     * This is the getter for _defaultImage
     * 
     * @return _defaultImage
     * @throws MediaFileException
     *             This method throws if the media for this drawable cant be
     *             found on disk.
     */
    public IViewImage getDefaultImage() {
        if (_defaultImage == null) {
            _defaultImage = _factory.makeImage( imagePath( _vars,
                getUniqueID(), _viewManager.getSize(), _viewManager
                        .getLanguage() ) );
        }
        return _defaultImage;
    }

    /**
     * This is the getter for _selectedImage
     * 
     * @return _selectedImage
     * @throws MediaFileException
     *             This method throws if the media for this drawable cant be
     *             found on disk.
     */
    public IViewImage getSelectedImage() {
        if (_selectedImage == null) {
            _selectedImage = _factory.makeImage( imagePath( _vars,
                getUniqueID() + "_selected", _viewManager.getSize(),
                _viewManager.getLanguage() ) );
        }
        return _selectedImage;
    }

    /**
     * This is the getter for _focusedImage
     * 
     * @return _focusedImage
     * @throws MediaFileException
     *             This method throws if the media for this drawable cant be
     *             found on disk.
     */
    public IViewImage getFocusedImage() {
        if (_focusedImage == null) {
            _focusedImage = _factory.makeImage( imagePath( _vars, getUniqueID()
                    + "_focused", _viewManager.getSize(), _viewManager
                    .getLanguage() ) );
        }
        return _focusedImage;
    }

    /**
     * This is the getter for _focusedSelectedImage
     * 
     * @return _focusedSelectedImage
     * @throws MediaFileException
     *             This method throws if the media for this drawable cant be
     *             found on disk.
     */
    public IViewImage getFocusedSelectedImage() {
        if (_focusedSelectedImage == null) {
            _focusedSelectedImage = _factory.makeImage( imagePath( _vars,
                getUniqueID() + "_focusedSelected", _viewManager.getSize(),
                _viewManager.getLanguage() ) );
        }
        return _focusedSelectedImage;
    }

    /**
     * This is the getter method for _focusedEvent.
     * 
     * @return This method returns the event that is raised when this toggle
     *         buttons switches to the focused state.
     */
    public Event getFocusedEvent() {
        return _focusedEvent;
    }

    /**
     * This is the getter method for _unfocusedEvent.
     * 
     * @return This method returns the event that is raised when this toggle
     *         buttons switches to the unfocused state.
     */
    public Event getUnfocusedEvent() {
        return _unfocusedEvent;
    }

    /**
     * This is the getter method for _selectedEvent.
     * 
     * @return This method returns the event that is raised when this toggle
     *         buttons switches to the selected state.
     */
    public Event getSelectedEvent() {
        return _selectedEvent;
    }

    /**
     * This is the getter method for _deselectedEvent.
     * 
     * @return This method returns the event that is raised when this toggle
     *         buttons switches to the deselected state.
     */
    public Event getDeselectedEvent() {
        return _deselectedEvent;
    }

    /**
     * @see votebox.middle.view.IFocusable#getUp()
     */
    public IFocusable getUp() {
        return _links.Up;
    }

    /**
     * @see votebox.middle.view.IFocusable#setUp(votebox.middle.view.IFocusable)
     */
    public void setUp(IFocusable focusable) {
        _links.Up = focusable;
    }

    /**
     * @see votebox.middle.view.IFocusable#getDown()
     */
    public IFocusable getDown() {
        return _links.Down;
    }

    /**
     * @see votebox.middle.view.IFocusable#setDown(votebox.middle.view.IFocusable)
     */
    public void setDown(IFocusable focusable) {
        _links.Down = focusable;
    }

    /**
     * @see votebox.middle.view.IFocusable#getLeft()
     */
    public IFocusable getLeft() {
        return _links.Left;
    }

    /**
     * @see votebox.middle.view.IFocusable#setLeft(votebox.middle.view.IFocusable)
     */
    public void setLeft(IFocusable focusable) {
        _links.Left = focusable;
    }

    /**
     * @see votebox.middle.view.IFocusable#getRight()
     */
    public IFocusable getRight() {
        return _links.Right;
    }

    /**
     * @see votebox.middle.view.IFocusable#setRight(votebox.middle.view.IFocusable)
     */
    public void setRight(IFocusable focusable) {
        _links.Right = focusable;
    }

    /**
     * @see votebox.middle.view.IFocusable#getNext()
     */
    public IFocusable getNext() {
        return _links.Next;
    }

    /**
     * @see votebox.middle.view.IFocusable#setNext(votebox.middle.view.IFocusable)
     */
    public void setNext(IFocusable focusable) {
        _links.Next = focusable;
    }

    /**
     * @see votebox.middle.view.IFocusable#getPrevious()
     */
    public IFocusable getPrevious() {
        return _links.Previous;
    }

    /**
     * @see votebox.middle.view.IFocusable#setPrevious(votebox.middle.view.IFocusable)
     */
    public void setPrevious(IFocusable focusable) {
        _links.Previous = focusable;
    }
}
