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

import votebox.middle.view.IViewImage;

/**
 * This class represents the default (neither focused nor selected) state of a
 * ToggleButton
 * 
 * @author Kyle
 * 
 */
public class DefaultToggleButtonState extends AToggleButtonState {

    /**
     * Singleton Design Pattern
     */
    public static final DefaultToggleButtonState Singleton = new DefaultToggleButtonState();

    /**
     * Singleton Design Pattern
     */
    private DefaultToggleButtonState() {}

    /**
     * @see votebox.middle.view.widget.AToggleButtonState#getImage(votebox.middle.view.widget.ToggleButton)
     */
    @Override
    public IViewImage getImage(ToggleButton context) {
        return context.getDefaultImage();
    }

    /**
     * @see votebox.middle.view.widget.AToggleButtonState#toggle(votebox.middle.view.widget.ToggleButton)
     */
    @Override
    public void select(ToggleButton context) {
        context.getGroup().select( context );
    }

    /**
     * @see votebox.middle.view.widget.AToggleButtonState#select(votebox.middle.view.widget.ToggleButton)
     */
    @Override
    public void makeSelected(ToggleButton context) {
        context.setState( SelectedToggleButtonState.Singleton );
        context.getSelectedEvent().notifyObservers();
    }

    /**
     * @see votebox.middle.view.widget.AToggleButtonState#deselect(votebox.middle.view.widget.ToggleButton)
     */
    @Override
    public void makeDeselected(ToggleButton context) {
    // NO-OP
    }

    /**
     * @see votebox.middle.view.widget.AToggleButtonState#focus(votebox.middle.view.widget.ToggleButton)
     */
    @Override
    public void focus(ToggleButton context) {
        context.setState( FocusedToggleButtonState.Singleton );
        context.getFocusedEvent().notifyObservers();
    }

    /**
     * @see votebox.middle.view.widget.AToggleButtonState#unfocus(votebox.middle.view.widget.ToggleButton)
     */
    @Override
    public void unfocus(ToggleButton context) {
    // NO-OP
    }

}
