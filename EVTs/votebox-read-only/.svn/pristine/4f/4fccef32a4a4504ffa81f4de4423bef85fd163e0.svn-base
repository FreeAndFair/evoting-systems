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

package auditorium;

/**
 * The auditorium integrity layer intefaces with an instance of this type in
 * order to access keys that are stored somehow.
 * 
 * @author kyle
 * 
 */
public interface IKeyStore {

    /**
     * Load the private key associated with a given ID.
     * 
     * @return This method returns the private key of the ID that was asked for.
     * @throws AuditoriumCryptoException
     *             This method throws if the file can't be found or if it isn't
     *             in the correct format.
     */
    Key loadKey(String nodeid) throws AuditoriumCryptoException;

    /**
     * Load a PEM certificate from a file.
     * 
     * @param nodeid
     *            Load this node's certificate.
     * @return This method returns the certificate that wasa loaded from the
     *         given file.
     */
    Cert loadCert(String nodeid) throws AuditoriumCryptoException;
    
    /**
     * Load the adder key associated with the given ID.
     */
    Object loadAdderKey(String nodeid) throws RuntimeException;
}
