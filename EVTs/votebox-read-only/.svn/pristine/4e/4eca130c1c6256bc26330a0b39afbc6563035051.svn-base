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

package verifier.util;

import java.util.*;

public class MemoryHole {
	private static final Runtime _runtime = Runtime.getRuntime();
	private static final java.util.Timer _scheduler = new java.util.Timer(true /*daemon*/);
	
	private static long _heap = 0;
	private static long _inuse = 0;
	private static long _inuseMax = 0;

	public static final int NUM_SAMPLES = 4096;
	
	private static long[] _heapSamples = new long[NUM_SAMPLES];
	private static long[] _inuseSamples = new long[NUM_SAMPLES];
	private static int _qhead = 0;
	private static long _count = 0;

	public synchronized static void sample() {
		_heap = _runtime.totalMemory();
		
		_inuse = _heap - _runtime.freeMemory();

		if (_inuse > _inuseMax) _inuseMax = _inuse;

		_heapSamples[_qhead] = _heap;
		_inuseSamples[_qhead] = _inuse;
		_qhead = (_qhead + 1) % NUM_SAMPLES;

		_count ++;
	}

	public static long getInUse() { return _inuse; }
	public static long getMaxInUse() { return _inuseMax; }
	public static long getHeap() { return _heap; }

	private static class SampleTask extends TimerTask {
		public SampleTask() { super(); }
		public void run() {
			sample();
		}
	}

	public static void scheduleSampler(long interval_ms) {
		_scheduler.scheduleAtFixedRate(new SampleTask(), 0, interval_ms);
	}

	public synchronized static long avgHeap() {
		int n = (_count < NUM_SAMPLES) ? (int)_count : NUM_SAMPLES;
		long sum = 0;
		for (int i = 0; i < n; i++) {
			sum += _heapSamples[i];
		}
		return sum / n;
	}

	public synchronized static long avgInUse() {
		int n = (_count < NUM_SAMPLES) ? (int)_count : NUM_SAMPLES;
		long sum = 0;
		for (int i = 0; i < n; i++) {
			sum += _inuseSamples[i];
		}
		return sum / n;
	}
};
