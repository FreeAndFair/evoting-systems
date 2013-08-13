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

package supervisor.model;

/**
 * The model of a VoteBox booth on the network
 * @author cshaw
 */
public class VoteBoxBooth extends AMachine {

    /**
     * Represents a VoteBox that is currently in use
     */
    public static final int IN_USE = 1;

    /**
     * Represents a VoteBox that is ready to be authorized
     */
    public static final int READY = 2;

    /**
     * Represents a VoteBox whose battery is low
     */
    @Deprecated
    public static final int BATTERY_LOW = 3;

    private int battery;

    private int protectedCount;

    private int publicCount;

    private byte[] currentNonce;

    /**
     * Constructs a new VoteBoxBooth
     * @param serial the serial number of the booth
     */
    public VoteBoxBooth(int serial) {
        super(serial);
    }

    /**
     * @return the battery level, as an integer [0..100]
     */
    public int getBattery() {
        return battery;
    }

    /**
     * @return the current nonce (if this machine is voting)
     */
    public byte[] getNonce() {
        return currentNonce;
    }

    /**
     * @return the protected count
     */
    public int getProtectedCount() {
        return protectedCount;
    }

    /**
     * @return the public count
     */
    public int getPublicCount() {
        return publicCount;
    }

    /**
     * Sets the battery level
     * @param battery the battery to set
     */
    public void setBattery(int battery) {
        this.battery = battery;
        obs.notifyObservers();
    }

    /**
     * Sets the machine's current nonce
     * @param nonce the currentNonce to set
     */
    public void setNonce(byte[] nonce) {
        this.currentNonce = nonce;
    }

    /**
     * Sets the machine's protected count
     * @param protectedCount the protectedCount to set
     */
    public void setProtectedCount(int protectedCount) {
        this.protectedCount = protectedCount;
        obs.notifyObservers();
    }

    /**
     * Sets the machine's public count
     * @param publicCount the publicCount to set
     */
    public void setPublicCount(int publicCount) {
        this.publicCount = publicCount;
        obs.notifyObservers();
    }

}
