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

package votebox;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.HashMap;

import votebox.middle.IVoteboxConstants;

import auditorium.IAuditoriumParams;

/**
 * This class reads constants
 * 
 * @author kyle
 * 
 */
public class AuditoriumParams implements IAuditoriumParams,
        IVoteboxConstants {

    public static final AuditoriumParams Singleton = new AuditoriumParams();

    public static final int DISCOVER_TIMEOUT = 4000;
    public static int DISCOVER_PORT = 9782;
    public static final int DISCOVER_REPLY_TIMEOUT = 1000;
    public static final int DISCOVER_REPLY_PORT = 9783;
    public static final int LISTEN_PORT = 9700;
    public static final int JOIN_TIMEOUT = 1000;
    public static final String BROADCAST_ADDRESS = "255.255.255.255";
    public static final String LOG_LOCATION = "log.out";
    public static final String KEYS_DIRECTORY = "/keys/";

    public static final String VIEW_IMPLEMENTATION = "SDL";
    public static final String RULE_FILE = "rules";
    
    //Default for cast_ballot_encryption_enabled.  Will probably need to be set to true in the future
    public static final boolean CAST_BALLOT_ENCRYPTION_ENABLED = false;
    
    //Default for use_commit_challenge_model.  Likewise, will probably be switched on in the future
    public static final boolean USE_COMMIT_CHALLENGE_MODEL = false;
    
    //If true will attempt to use SDL to enable the touchscreen.  Should not be set if not using SDL view.
    public static final boolean USE_ELO_TOUCH_SCREEN = false;
    
    //The path to use to the Elo touchscreen if USE_ELO_TOUCH_SCREEN is true
    public static final String ELO_TOUCH_SCREEN_DEVICE = null;
    
    public static final int VIEW_RESTART_TIMEOUT = 5000;
    
    //Default for default serial number, -1 indicates that it MUST be specified explicitly somehow
    public static final int DEFAULT_SERIAL_NUMBER = -1;
    
    //Default report address, used exclusively by tap.  if "", must be specified explicitly somehow.
    public static final String DEFAULT_REPORT_ADDRESS = "";
    
    //Default challenge port, used by challenge web server and tap.  If -1, must be specified explicitly somehow.
    public static final int DEFAULT_CHALLENGE_PORT = -1;
    
    //Default http port, used by challenge web server.
    public static final int DEFAULT_HTTP_PORT = 80;
    
    //Default challenge ballot file.  If "", must be specified explicitly somehow.
    public static final String DEFAULT_BALLOT_FILE = "";
    
    //Default printer for VVPAT. If "", do not use VVPAT.
    public static final String PRINTER_FOR_VVPAT = "";
    
    //Default page size for VVPAT.  Based off of Star TPS800 model printer.
    public static final int PAPER_WIDTH_FOR_VVPAT = 249;
    public static final int PAPER_HEIGHT_FOR_VVPAT = 322;
    
    //Default imageable area for VVPAT.  Based off of Star TPS800 model printer.
    public static final int PRINTABLE_WIDTH_FOR_VVPAT = 239;
    public static final int PRINTABLE_HEIGHT_FOR_VVPAT = 311;
    
    //By default, we don't enable NIZKs.
    public static final boolean ENABLE_NIZKS = false;
    
    //By default, we don't enable Piecemeal Encryption
    public static final boolean USE_PIECEMEAL_ENCRYPTION = false;
    
    //By default, we use the "fanciest" tally view possible
    public static final boolean USE_SIMPLE_TALLY_VIEW = false;
    public static final boolean USE_TABLE_TALLY_VIEW = false;
    
    //AWT view is windowed by default (as it may break if fullscreen
    public static final boolean DEFAULT_USE_WINDOWED_VIEW = true;
    
    public static final boolean DEFAULT_ALLOW_UI_SCALING = true;
    
    private final HashMap<String, String> _config;

    /**
     * @param path
     *            Read configuration from this path
     */
    public AuditoriumParams(String path) {
        _config = new HashMap<String, String>();

        read( path );
    }

    private AuditoriumParams() {
        _config = new HashMap<String, String>();
    }

    public String getBroadcastAddress() {
        if (_config.containsKey( "BROADCAST_ADDRESS" ))
            return _config.get( "BROADCAST_ADDRESS" );
        return BROADCAST_ADDRESS;
    }

    public int getDiscoverPort() {
        if (_config.containsKey( "DISCOVER_PORT" ))
            return Integer.parseInt( _config.get( "DISCOVER_PORT" ) );
        return DISCOVER_PORT;
    }

    public int getDiscoverReplyPort() {
        if (_config.containsKey( "DISCOVER_REPLY_PORT" ))
            return Integer.parseInt( _config.get( "DISCOVER_REPLY_PORT" ) );
        return DISCOVER_REPLY_PORT;
    }

    public int getDiscoverReplyTimeout() {
        if (_config.containsKey( "DISCOVER_REPLY_TIMEOUT" ))
            return Integer.parseInt( _config.get( "DISCOVER_REPLY_TIMEOUT" ) );
        return DISCOVER_REPLY_TIMEOUT;
    }

    public int getDiscoverTimeout() {
        if (_config.containsKey( "DISCOVER_TIMEOUT" ))
            return Integer.parseInt( _config.get( "DISCOVER_TIMEOUT" ) );
        return DISCOVER_TIMEOUT;
    }

    public int getJoinTimeout() {
        if (_config.containsKey( "JOIN_TIMEOUT" ))
            return Integer.parseInt( _config.get( "JOIN_TIMEOUT" ) );
        return JOIN_TIMEOUT;
    }

    public int getListenPort() {
        if (_config.containsKey( "LISTEN_PORT" ))
            return Integer.parseInt( _config.get( "LISTEN_PORT" ) );
        return LISTEN_PORT;
    }

    public String getLogLocation() {
        if (_config.containsKey( "LOG_LOCATION" ))
            return _config.get( "LOG_LOCATION" );
        return LOG_LOCATION;
    }

    public String getViewImplementation() {
        if (_config.containsKey( "VIEW_IMPLEMENTATION" ))
            return _config.get( "VIEW_IMPLEMENTATION" );
        return VIEW_IMPLEMENTATION;
    }

    public auditorium.IKeyStore getKeyStore() {
        String kd = KEYS_DIRECTORY;
        if (_config.containsKey( "KEYS_DIRECTORY" ))
            kd =_config.get( "KEYS_DIRECTORY" );
        return new auditorium.SimpleKeyStore(kd);
    }
    
    public String getRuleFile() {
        if (_config.containsKey( "RULE_FILE" ))
            return _config.get( "RULE_FILE" );
        return RULE_FILE;
    }


	public boolean getCastBallotEncryptionEnabled() {
		if(_config.containsKey("CAST_BALLOT_ENCRYPTION_ENABLED"))
			return Boolean.parseBoolean(_config.get("CAST_BALLOT_ENCRYPTION_ENABLED"));
		
		return CAST_BALLOT_ENCRYPTION_ENABLED;
	}
	
	public boolean getUseCommitChallengeModel(){
		if(_config.containsKey("USE_COMMIT_CHALLENGE_MODEL"))
			return Boolean.parseBoolean(_config.get("USE_COMMIT_CHALLENGE_MODEL"));
		
		return USE_COMMIT_CHALLENGE_MODEL;
	}
    
	public boolean getUseEloTouchScreen(){
		if(_config.containsKey("USE_ELO_TOUCH_SCREEN"))
			return Boolean.parseBoolean(_config.get("USE_ELO_TOUCH_SCREEN"));
		
		return USE_ELO_TOUCH_SCREEN;
	}//getUseEloTouchScreen
	
	public String getEloTouchScreenDevice(){
		if(_config.containsKey("ELO_TOUCH_SCREEN_DEVICE"))
			return (String)_config.get("ELO_TOUCH_SCREEN_DEVICE");
		
		return ELO_TOUCH_SCREEN_DEVICE;
	}//getEloTouchScreenDevice
	
	public int getViewRestartTimeout(){
		if(_config.containsKey("VIEW_RESTART_TIMEOUT"))
			return Integer.parseInt((String)_config.get("VIEW_RESTART_TIMEOUT"));
		
		return VIEW_RESTART_TIMEOUT;
	}//getViewRestartTimeout


	public int getDefaultSerialNumber() {
		if(_config.containsKey("DEFAULT_SERIAL_NUMBER"))
			return Integer.parseInt((String)_config.get("DEFAULT_SERIAL_NUMBER"));
		
		return DEFAULT_SERIAL_NUMBER;
	}
	
	public String getReportAddress(){
		if(_config.containsKey("DEFAULT_REPORT_ADDRESS"))
			return (String)_config.get("DEFAULT_REPORT_ADDRESS");
		
		return DEFAULT_REPORT_ADDRESS;
	}
	
	public int getChallengePort(){
		if(_config.containsKey("DEFAULT_CHALLENGE_PORT"))
			return Integer.parseInt((String)_config.get("DEFAULT_CHALLENGE_PORT"));
		
		return DEFAULT_CHALLENGE_PORT;
	}
	
	public int getHttpPort(){
		if(_config.containsKey("DEFAULT_HTTP_PORT"))
			return Integer.parseInt((String)_config.get("DEFAULT_HTTP_PORT"));
		
		return DEFAULT_HTTP_PORT;
	}
	
	public String getChallengeBallotFile(){
		if(_config.containsKey("DEFAULT_BALLOT_FILE"))
			return (String)_config.get("DEFAULT_BALLOT_FILE");
		
		return DEFAULT_BALLOT_FILE;
	}
	
	public String getPrinterForVVPAT() {
		if(_config.containsKey("PRINTER_FOR_VVPAT"))
			return (String)_config.get("PRINTER_FOR_VVPAT");
		
		return PRINTER_FOR_VVPAT;
	}
	
	public int getPaperHeightForVVPAT() {
		try{
			if(_config.containsKey("PAPER_HEIGHT_FOR_VVPAT"))
				return Integer.parseInt(_config.get("PAPER_HEIGHT_FOR_VVPAT"));
		}catch(NumberFormatException e){}
		
		return PAPER_HEIGHT_FOR_VVPAT;
	}

	public int getPaperWidthForVVPAT() {
		try{
			if(_config.containsKey("PAPER_WIDTH_FOR_VVPAT"))
				return Integer.parseInt(_config.get("PAPER_WIDTH_FOR_VVPAT"));
		}catch(NumberFormatException e){}
		
		return PAPER_WIDTH_FOR_VVPAT;
	}

	public int getPrintableHeightForVVPAT() {
		try{
			if(_config.containsKey("PRINTABLE_HEIGHT_FOR_VVPAT"))
				return Integer.parseInt(_config.get("PRINTABLE_HEIGHT_FOR_VVPAT"));
		}catch(NumberFormatException e){}
		
		return PRINTABLE_HEIGHT_FOR_VVPAT;
	}

	public int getPrintableWidthForVVPAT() {
		try{
			if(_config.containsKey("PRINTABLE_WIDTH_FOR_VVPAT"))
				return Integer.parseInt(_config.get("PRINTABLE_WIDTH_FOR_VVPAT"));
		}catch(NumberFormatException e){}
		
		return PRINTABLE_WIDTH_FOR_VVPAT;
	}
	
	public boolean getEnableNIZKs() {
		if(_config.containsKey("ENABLE_NIZKS"))
			return Boolean.parseBoolean(_config.get("ENABLE_NIZKS"));
		
		return ENABLE_NIZKS;
	}
	
	public boolean getUsePiecemealEncryption(){
		if(_config.containsKey("USE_PIECEMEAL_ENCRYPTION"))
			return Boolean.parseBoolean(_config.get("USE_PIECEMEAL_ENCRYPTION"));
		
		return USE_PIECEMEAL_ENCRYPTION;
	}
	
	public boolean getUseSimpleTallyView(){
		if(_config.containsKey("USE_SIMPLE_TALLY_VIEW"))
			return Boolean.parseBoolean(_config.get("USE_SIMPLE_TALLY_VIEW"));
		
		return USE_SIMPLE_TALLY_VIEW;
	}
    
    public boolean getUseTableTallyView(){
    	if(_config.containsKey("USE_TABLE_TALLY_VIEW"))
			return Boolean.parseBoolean(_config.get("USE_TABLE_TALLY_VIEW"));
		
		return USE_TABLE_TALLY_VIEW;
    }
    
    public boolean getUseWindowedView(){
    	if(_config.containsKey("USE_WINDOWED_VIEW"))
    		return Boolean.parseBoolean(_config.get("USE_WINDOWED_VIEW"));
    	
    	return DEFAULT_USE_WINDOWED_VIEW;
    }
    
    public boolean getAllowUIScaling(){
    	if(_config.containsKey("ALLOW_UI_SCALING"))
    		return Boolean.parseBoolean(_config.get("ALLOW_UI_SCALING"));
    	
    	return DEFAULT_ALLOW_UI_SCALING;
    }
	
    /**
     * Read from the configuration file.
     */
    private void read(String path) {
        try {
            BufferedReader reader = new BufferedReader( new InputStreamReader(
                    new FileInputStream( new File( path ) ) ) );
            
            ArrayList<String> content = new ArrayList<String>();
            String temp;
            while ((temp = reader.readLine()) != null) {
            	temp = temp.trim();
            	
            	//read lines that start with "#" as comments, and thus ignore
            	if (temp.startsWith("#")) continue;
            	//ignore lines that are just newlines
            	//ignore the rest of the line if it is a comment
            	if (temp.indexOf('#') > -1) temp = temp.substring(0, temp.indexOf('#'));
            	
            	if(temp.length() > 0)
            		content.add(temp.trim());
            }
            
            if (content.size() % 2 == 1)
            	throw new RuntimeException(
                        "Couldn't parse the configuration file.", null );
            
            for (int i = 0; i < content.size(); i += 2)
            	_config.put(content.get(i), content.get(i + 1));
        }
        catch (IOException e) {
            System.err
                    .println( "Couldn't parse the configuration file, using defaults: "
                            + e.getMessage() );
        }
    }
}
