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

package sim.pseupervisor;

import sim.utils.*;

import supervisor.model.*;

import votebox.*;

import java.util.*;
import java.io.*;
import java.math.BigInteger;

public class Pseupervisor {
	static String OPT_AUTHORIZE_PERIOD_MIN = "auth-period-min";
	static String OPT_AUTHORIZE_PERIOD_MAX = "auth-period-max";
	static String OPT_OPEN_POLLS_TIME = "open-polls-time";
	static String OPT_CLOSE_POLLS_TIME = "close-polls-time";

	static String OPT_MACHINE_ID = "id";
	static String OPT_BALLOT_FILE = "ballot";
	static String OPT_PARAMS_FILE = "conf";

	static HashMap<String, Object> kDefaultOptions;
	static {
		kDefaultOptions = new HashMap<String, Object>();
		kDefaultOptions.put(OPT_AUTHORIZE_PERIOD_MIN, 1 * Time.MINUTES);
		kDefaultOptions.put(OPT_AUTHORIZE_PERIOD_MAX, 10 * Time.MINUTES);
		kDefaultOptions.put(OPT_OPEN_POLLS_TIME, 5 * Time.MINUTES);
		kDefaultOptions.put(OPT_CLOSE_POLLS_TIME, 1 * Time.HOURS + 5 * Time.MINUTES);
		kDefaultOptions.put(OPT_MACHINE_ID, 0);
		kDefaultOptions.put(OPT_BALLOT_FILE, "ballot.zip");
		kDefaultOptions.put(OPT_PARAMS_FILE, "supervisor.conf");
	}

	static long t0;

	/**
	 * @param args
	 */
	public static void main(String[] args) 
		throws InterruptedException
	{
		HashMap<String, Object> opts 
			= new HashMap<String, Object>(kDefaultOptions);

		ArgParse.addArgsToMap(args, opts);

		if (! new File(opts.get(OPT_BALLOT_FILE).toString()).exists()) {
			System.err.println("warning: ballot file does not appear to exist: " + opts.get(OPT_BALLOT_FILE).toString());
		}

		if (! new File(opts.get(OPT_PARAMS_FILE).toString()).exists()) {
			System.err.println("warning: config file '"
				+ opts.get(OPT_PARAMS_FILE) + "' does not appear to exist");
		}

		Model model = new Model(
			new Integer(opts.get(OPT_MACHINE_ID).toString()),
			new AuditoriumParams(opts.get(OPT_PARAMS_FILE).toString())
		);
		model.setBallotLocation(opts.get(OPT_BALLOT_FILE).toString());

		// model.addListener(new VoteBoxEventListener() {
			// public void castBallot(CastBallotEvent e) {
				// System.out.println("Got cast ballot: " + e.toString());
			// }
		// });

		// final HashSet<int> machine_ids = new HashSet<int>();
		// model.registerForMachinesChanged(new Observer() {
			// void update(Observable o, Object arg) {
			// }
		// });

		System.out.println("Starting supervisor model.");
		model.start();

		t0 = System.currentTimeMillis();
		Random rand = new Random();

		System.out.println("Opening polls in " + opts.get(OPT_OPEN_POLLS_TIME) + " ms.");

		Thread.sleep(new Integer(opts.get(OPT_OPEN_POLLS_TIME).toString()));
		
		System.out.println("Activating supervisor.");
		model.activate();

		final Model _m = model; // stupid
		new Thread() {
			public void run() {
				System.out.println("Opening polls.");
				_m.openPolls();
			}
		}.start();

		System.out.println("Casting ballots for " + opts.get(OPT_CLOSE_POLLS_TIME) + " ms.");

		long closeTime = new Integer(opts.get(OPT_CLOSE_POLLS_TIME).toString());
		long authPeriodMin = new Integer(opts.get(OPT_AUTHORIZE_PERIOD_MIN).toString());
		long authPeriodMax = new Integer(opts.get(OPT_AUTHORIZE_PERIOD_MAX).toString());

		int ballotsAuthorized = 0;

		while ((System.currentTimeMillis() - t0) < (closeTime - authPeriodMax))
		{
			long duration = authPeriodMin
				+ (long)(rand.nextFloat() * (authPeriodMax - authPeriodMin));
			System.out.println("sleeping " + duration + " ms");
			Thread.sleep(duration);
			
			ArrayList<AMachine> availableMachines = new ArrayList<AMachine>();

			for (AMachine m : model.getMachines()) {
				if (m instanceof VoteBoxBooth
					&& m.getStatus() == VoteBoxBooth.READY)
				{
					availableMachines.add(m);
				}
			}
			if (availableMachines.size() == 0) {
				System.out.println("note: not authorizing any ballots this turn, because there are no available booths right now.");
			} else {
				AMachine aMachine = availableMachines.get(
					rand.nextInt(availableMachines.size()));

				System.out.println("Authorizing ballot on booth " + aMachine + " (ID " + aMachine.getSerial() + ")");

				try {
					model.authorize(aMachine.getSerial());
					ballotsAuthorized += 1;
				} catch (IOException e) {
					System.err.println("error authorizing vote (probably missing ballot file): ");
					e.printStackTrace();
				}
			}
		}

		System.out.println("Authorized a total of " + ballotsAuthorized + " ballots. Closing polls.");

		new Thread() {
			public void run() {
				System.out.println("Closing polls.");
				Map<String, BigInteger> results = _m.closePolls();
				System.out.println("Results: " + results);
			}
		}.start();

		Thread.sleep(1 * Time.MINUTES);

		System.out.println("Stopping Auditorium.");
		model.getAuditoriumConnector().disconnect();

		System.exit(0);
	}
}
