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
 * These are configuration constants that auditorium needs. Pass an instance of
 * this to an {@link AuditoriumHost} when you construct it.
 * 
 * @author kyle
 * @see auditorium.AuditoriumHost
 */
public interface IAuditoriumParams {

    /**
     * @return Timeout after this many miliseconds when listening for discover
     *         responses.
     */
    public int getDiscoverTimeout();

    /**
     * @return Discover requests should be UDP broadcast on this port.
     */

    public int getDiscoverPort();

    /**
     * @return Timeout after this many miliseconds when trying to reply to a
     *         discover request.
     */

    public int getDiscoverReplyTimeout();

    /**
     * @return Discover replies should be sent over a TCP socket established at
     *         this port.
     */
    public int getDiscoverReplyPort();

    /**
     * @return Hosts should listen on this port for incoming join requests.
     */
    public int getListenPort();

    /**
     * @return If you don't get a reply back from the join in this amount of
     *         time, give up.
     */

    public int getJoinTimeout();

    /**
     * @return Send UDP packets to this address as "broadcast"
     */
    public String getBroadcastAddress();

    /**
     * @return Create the log data here.
     */
    public String getLogLocation();

    /**
	 * @return Return an {@link auditorium.IKeyStore} to be used when looking for
	 *         certificates of other participants or signing authorities.
	 */
    public IKeyStore getKeyStore();

    /**
	 * @return This method returns the location of the file that defines the
	 *         rule that should be given to an instance of {@link verifier.Verifier}.
	 *         Return null to denote that the verifier should not be used.
	 */
    public String getRuleFile();
    
    /**
     * @return Returns true if encryption for cast ballots is enabled.  This is used to determine the
     *         Tallier to use in the Supervisor, and the cast-ballot message to send from
     *         VoteBox.
     */
    public boolean getCastBallotEncryptionEnabled();

    /**
     * 
     * @return Returns true if VoteBox should make use of the "commit-challenge" model for voting.
     * 		   If false, a single event is used for casting ballots in place of the two stage
     * 	 	   commit & cast.
     */
    public boolean getUseCommitChallengeModel();
    
    /**
     * @return Returns true if VoteBox should use SDL to connect toe an Elo touchscreen as an input device.
     *         Should only be true on linux, SDL view, framebuffer driven machines.  All other configurations
     *         are likely to fail, and ungracefully at that.
     */
    public boolean getUseEloTouchScreen();
    
    /**
     * 
     * @return Return the path to the Elo touch screen.  Used by SDL to connect to that device for mouse input.
     */
    public String getEloTouchScreenDevice();
    
    /**
     * 
     * @return the amount of time (in milliseconds) the view should wait before restarting after
     *         a successful vote.
     */
    public int getViewRestartTimeout();
    
    /**
     * @return the key to use (if not specified on the command line).
     */
    public int getDefaultSerialNumber();
    
    /**
     * @return the report address for Tap to use (if not specified on the command line).
     */
    public String getReportAddress();
    
    /**
     * @return the port for the challenge web server and tap to use to communicate (if not specified on the command line).
     */
    public int getChallengePort();
    
    /**
     * @return the port for the challenge web server to server http requests on.
     */
    public int getHttpPort();
    
    /**
     * @return the ballot file to be used for images by the challenge web server (if not specified on the command line).
     */
    public String getChallengeBallotFile();
    
    /**
     * @return the name of the VVPAT printer to use, if any
     */
    public String getPrinterForVVPAT();
    
    /**
     * @return the width of the page (in 1/72nds of an inch) in use on the VVPAT printer.
     */
    public int getPaperWidthForVVPAT();
    
    /**
     * @return the height of the page (in 1/72nds of an inch) in use on the VVPAT printer.
     */
    public int getPaperHeightForVVPAT();
    
    /**
     * @return the width of the printable area (in 1/72nds of an inch) of the page on the VVPAT printer.
     */
    public int getPrintableWidthForVVPAT();
    
    /**
     * @return the height of the printable area (in 1/72nds of an inch) of the page on the VVPAT printer.
     */
    public int getPrintableHeightForVVPAT();
    
    /**
     * @return true if VoteBox should use NIZKs to confirm the wellformed-ness of ballots.
     */
    public boolean getEnableNIZKs();
    
    /**
     * @return true if VoteBox should use piecemeal encryption to improve the user's perceived "time to vote".
     */
    public boolean getUsePiecemealEncryption();
    
    /**
     * @return true if Supervisor should display the tally results in the simplest way it can.
     */
    public boolean getUseSimpleTallyView();
    
    /**
     * @return true if Supervisor should display the tally results in a image-laden table, if possible.
     */
    public boolean getUseTableTallyView();
    
    /**
     * @return true if VoteBox should try and use a windows view.
     */
    public boolean getUseWindowedView();
    
    /**
     * @return true if the AWT VoteBox UI should attempt to scale a ballot to fit the screen
     */
    public boolean getAllowUIScaling();
}
