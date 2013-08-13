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

package auditorium.test;

import auditorium.IAuditoriumParams;

/**
 * Implementation of IAuditoriumParams for use in test cases. The log is
 * saved in <tt>/tmp</tt>.
 * 
 * @see votebox.AuditoriumParams for the concrete implementation used in live
 *      VoteBox.
 * @author dsandler
 * 
 */
public class TestParams implements IAuditoriumParams {

    public static final TestParams Singleton = new TestParams();

    /*
     * Values originally taken from AuditoriumParams.java to be representative
     * of VoteBox.
     */
    public static final int DISCOVER_TIMEOUT = 4000;
    public static int DISCOVER_PORT = 9782;
    public static final int DISCOVER_REPLY_TIMEOUT = 1000;
    public static final int DISCOVER_REPLY_PORT = 9783;
    public static final int LISTEN_PORT = 9700;
    public static final int JOIN_TIMEOUT = 1000;
    public static final String BROADCAST_ADDRESS = "255.255.255.255";
    public static final String LOG_LOCATION = "/local/derrley/log.out";
    public static final String KEYS_DIRECTORY = "/keys/";
    public static final String RULE_FILE = "rules";
    public static final boolean ENCRYPTION_ENABLED = false;
    public static final boolean USE_COMMIT_CHALLENGE_MODEL = false;
    public static final boolean USE_ELO_TOUCH_SCREEN = false;
	public static final String ELO_TOUCH_SCREEN_DEVICE = null;
	public static final int VIEW_RESTART_TIMEOUT = 5000;
	public static final int DEFAULT_SERIAL_NUMBER = -1;
	public static final String DEFAULT_REPORT_ADDRESS = "";
    public static final int DEFAULT_CHALLENGE_PORT = -1;
    public static final int DEFAULT_HTTP_PORT = 80;
    public static final String DEFAULT_BALLOT_FILE = "";
    public static final String DEFAULT_PRINTER_FOR_VVPAT = "";
    public static final boolean DEFAULT_ENABLE_NIZKS = false;
    public static final boolean DEFAULT_USE_PIECEMEAL_ENCRYPTION = false;
    public static final boolean DEFAULT_USE_SIMPLE_TALLY_VIEW = false;
    public static final boolean DEFAULT_USE_TABLE_TALLY_VIEW = false;
    public static final boolean DEFAULT_USE_WINDOWED_VIEW = true;
    public static final boolean DEFAULT_ALLOW_UI_SCALING = true;

    public String getBroadcastAddress() {
        return BROADCAST_ADDRESS;
    }

    public int getDiscoverPort() {
        return DISCOVER_PORT;
    }

    public int getDiscoverReplyPort() {
        return DISCOVER_REPLY_PORT;
    }

    public int getDiscoverReplyTimeout() {
        return DISCOVER_REPLY_TIMEOUT;
    }

    public int getDiscoverTimeout() {
        return DISCOVER_TIMEOUT;
    }

    public int getJoinTimeout() {
        return JOIN_TIMEOUT;
    }

    public int getListenPort() {
        return LISTEN_PORT;
    }

    public String getLogLocation() {
        return LOG_LOCATION;
    }

    public auditorium.IKeyStore getKeyStore() {
        return new auditorium.SimpleKeyStore(KEYS_DIRECTORY);
    }

    public String getRuleFile() {
        return RULE_FILE;
    }

	public boolean getCastBallotEncryptionEnabled() {
		return ENCRYPTION_ENABLED;
	}
	
	public boolean getUseCommitChallengeModel(){
		return USE_COMMIT_CHALLENGE_MODEL;
	}

	public boolean getUseEloTouchScreen() {
		return USE_ELO_TOUCH_SCREEN;
	}
	
	public String getEloTouchScreenDevice() {
		return ELO_TOUCH_SCREEN_DEVICE ;
	}
	
	public int getViewRestartTimeout(){
		return VIEW_RESTART_TIMEOUT;
	}
	
	public int getDefaultSerialNumber(){
		return DEFAULT_SERIAL_NUMBER;
	}

	public int getChallengePort() {
		return DEFAULT_CHALLENGE_PORT;
	}

	public String getReportAddress() {
		return DEFAULT_REPORT_ADDRESS;
	}
	
	public int getHttpPort(){
		return DEFAULT_HTTP_PORT;
	}
	
	public String getChallengeBallotFile(){
		return DEFAULT_BALLOT_FILE;
	}

	public String getPrinterForVVPAT() {
		return DEFAULT_PRINTER_FOR_VVPAT;
	}

	public int getPaperHeightForVVPAT() {
		return 0;
	}

	public int getPaperWidthForVVPAT() {
		return 0;
	}

	public int getPrintableHeightForVVPAT() {
		return 0;
	}

	public int getPrintableWidthForVVPAT() {
		return 0;
	}

	public boolean getEnableNIZKs() {
		return DEFAULT_ENABLE_NIZKS;
	}
	
	public boolean getUsePiecemealEncryption()
	{
		return DEFAULT_USE_PIECEMEAL_ENCRYPTION;
	}

	public boolean getUseSimpleTallyView() {
		return DEFAULT_USE_SIMPLE_TALLY_VIEW;
	}

	public boolean getUseTableTallyView() {
		return DEFAULT_USE_TABLE_TALLY_VIEW;
	}
	
	public boolean getUseWindowedView(){
		return DEFAULT_USE_WINDOWED_VIEW;
	}
	
	public boolean getAllowUIScaling(){
		return DEFAULT_ALLOW_UI_SCALING;
	}
}
