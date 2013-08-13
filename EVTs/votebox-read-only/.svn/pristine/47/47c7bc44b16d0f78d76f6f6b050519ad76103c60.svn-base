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

package verifier;

/**
 * Plugins to the verifier must implement this interface.<br>
 * <br>
 * When the verifier is run as a standalone application, each plugin's
 * initialize method will be called only once near the start of the verifier's
 * running.When the verifier is run as a module, the initialize method will be
 * called once (in a similar fashion) but the application will gain a reference
 * to the plugin after it is loaded, and is free to make specific API calls to
 * the plugin as it sees fit.
 * 
 * @see verifier.Verifier
 * @author kyle
 * 
 */
public interface IVerifierPlugin {

    /**
     * This method will be called from the verifier once after the plugin is
     * constructed.
     * 
     * @param verifier
     *            This is the verifier instance that is constructing this
     *            plugin.
     * @throws PluginException
     *             This method throws if the plugin encountered problems.
     */
    public abstract void init(Verifier verifier) throws PluginException;
}
