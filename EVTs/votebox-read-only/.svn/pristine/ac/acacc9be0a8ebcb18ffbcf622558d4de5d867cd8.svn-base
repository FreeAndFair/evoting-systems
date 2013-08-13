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

import java.util.Observable;

/**
 * Because this code was originally designed for C#, there are a few places that
 * use the C# event primitive. This implementation of a java Observable provides
 * the same behavior. Call Event.addObserver(...) to add callbacks. Call
 * Event.notifyObservers() to invoke all of them.
 * 
 * @author Kyle
 * 
 */
public class Event extends Observable {

    /**
     * Call this method to immediately invoke the update(...) method on every
     * observer.
     * 
     * @see java.util.Observable#notifyObservers()
     */
    @Override
    public void notifyObservers() {
        setChanged();
        super.notifyObservers();
    }

    /**
     * Call this method to immediately invoke the update(...) method on every
     * observer.
     * 
     * @see java.util.Observable#notifyObservers()
     */
    @Override
    public void notifyObservers(Object arg) {
        setChanged();
        super.notifyObservers( arg );
    }

}
