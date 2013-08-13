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

import java.io.*;
import java.util.*;
import sexpression.*;
import sexpression.stream.*;
import verifier.ast.*;
import verifier.value.*;

import verifier.util.*;

/** example command line:
 *
 *  java -cp build verifier.IncrcmentalStepVerifier incr=40 rule=rules/voting2.rules  log=logdata/20070929-superlog.out  plugin=votebox.auditoriumverifierplugins.IncrementalAuditoriumLog
 */
public class IncrementalStepVerifier extends Verifier {
    static ThreadTimer timer = null;
    static ThreadTimer totalTime = null;
    static Verifier v = null;
    static IIncrementalPlugin plugin = null;
    static ASExpression rule = null;
    static int totalCount = 0;
    static Value lastResult = null;
    static String logFile = null;
    static ASEInputStreamReader logInput;
	static boolean useDagCache = false;
    
	static HashMap<String, String> argmap;

    public static void reset() throws Exception {
		System.out.printf("# resetting all verifier state\n");

        v = new Verifier(argmap);

		timer.start();
    		plugin.init(v);
		timer.stop();
		System.out.printf("[TIME] plugin.init: %d ms\n", timer.lookMilli());

		logInput = new ASEInputStreamReader(
				new FileInputStream(new File(logFile)));

		// prime the evaluator
		timer.start();
    		lastResult = v.eval( rule ); // probably a reduction
		timer.stop();
		//System.out.println( "# RESULT = " + lastResult );
		//System.out.printf( "# ASSERTION FAILURES: %d\n",
		//	Assert.FAILED_ASSERTIONS.size() );
		//for (AssertionFailure f : Assert.FAILED_ASSERTIONS)
		//	System.out.printf( "#   --> %s\n", f.toString() );
		System.out.printf("[TIME] initial-eval: %d ms\n", timer.lookMilli());
		
		totalCount = 0;
    }
    
	public static void main(String[] args) throws Exception {
		timer = ThreadTimer.timerForCurrentThread();
		totalTime = ThreadTimer.timerForCurrentThread();

		argmap = parseArgs( args );

        if (!argmap.containsKey( "incr" ))
            argNotFound( "incr (# of entries between verifier runs -- set to 0 to run monolithically)" );
        if (!argmap.containsKey( "rule" ))
            argNotFound( "rule (path to rules file)" );
        if (!argmap.containsKey( "log" ))
            argNotFound( "log (path to log file)" );
		if (!argmap.containsKey("plugin")) 
			argNotFound("plugin (name of IVerifierPlugin instance)");
		
		System.out.printf("# running with args:");
		for (String a : argmap.keySet()) {
			System.out.printf(" %s=%s", a, argmap.get(a));
		}
		System.out.printf("\n");

        int incr = new Integer(argmap.get("incr")).intValue();
		if (incr < 0) throw new RuntimeException("incr cannot be < 0");
		System.out.printf("# increment: %d\n", incr);
		
		logFile = argmap.get("log");
		
		// should we reset the evaluator every round, as if we didn't have
		// incremental evaluation?
		boolean restartEveryTime = false;
		if (argmap.containsKey("restart"))
		    restartEveryTime = new Boolean(argmap.get("restart")).booleanValue();
		else if (argmap.containsKey("reset"))
		    restartEveryTime = new Boolean(argmap.get("reset")).booleanValue();

		if (argmap.containsKey("dagcache"))
		    useDagCache = new Boolean(argmap.get("dagcache")).booleanValue();

		if (restartEveryTime) 
		    System.out.printf("# pretending we don't have incremental; restarting every time\n");

		// initialize the plugin
		String pluginClassName = argmap.get("plugin");
		plugin 
			= (IIncrementalPlugin)Class.forName(pluginClassName).newInstance();

		// ------------------------------------------------------------
		MemoryHole.scheduleSampler(2 * 1000); // 2 sec
		totalTime.start();

        timer.start();
            rule = readRule( argmap.get( "rule" ) );
		timer.stop();

		System.out.printf("[TIME] readRule: %d ms\n", timer.lookMilli());

		boolean done = false;

        if (!restartEveryTime)
            // we only do this once unless we're simulating monolithic eval
            reset();

        int loops = 0;
		while (!done && 
				(incr == 0 
				    || restartEveryTime
					|| lastResult == null 
					|| lastResult instanceof Reduction))
		{
		    loops++;
		    
		    if (restartEveryTime)
		        reset();
		        
		    int i = 0;
			timer.start();
			{
    			try {
    				while ((incr == 0) || (i < incr)
    				    || (restartEveryTime && (i < loops*incr)))
    				{
    					ASExpression msg = logInput.read();
    					plugin.addLogData(msg);
    					totalCount++;
    					i++;
    				}
    			} catch (EOFException e) {
    				done = true;
    				System.out.printf("# CLOSING LOG\n");
    				plugin.closeLog();
    			}
            }
			timer.stop();
			System.out.printf("[TIME] read and add (%d events): %d ms\n",
				i, timer.lookMilli());

			if (restartEveryTime) {
				System.out.printf("# CLOSING LOG (for now...)\n");
			    plugin.closeLog();
			}

			timer.start();
			    lastResult = v.eval( ((Reduction)lastResult).getAST() );
			timer.stop();
			System.out.println( "# RESULT = " + lastResult );
			System.out.printf( "# ASSERTION FAILURES: %d\n",
				Assert.FAILED_ASSERTIONS.size() );
			for (AssertionFailure f : Assert.FAILED_ASSERTIONS)
				System.out.printf( "#   --> %s\n", f.toString() );
			System.out.printf("[TIME] eval: %d ms\n", timer.lookMilli());
		}
		
		System.out.printf("# processed %d events\n", totalCount);
		System.out.printf("[TIME] total: %d ms\n", totalTime.lookMilli());

		System.out.printf("[MEM] current inUse: %d heap: %d\n",
			MemoryHole.getInUse(), MemoryHole.getHeap());
		System.out.printf("[MEM] maxInUse: %d\n", MemoryHole.getMaxInUse());
		System.out.printf("[MEM] avgInUse: %d\n", MemoryHole.avgInUse());
	}
}
