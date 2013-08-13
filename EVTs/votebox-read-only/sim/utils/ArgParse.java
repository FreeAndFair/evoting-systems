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

package sim.utils;

import java.util.*;

public class ArgParse {
	@SuppressWarnings("serial")
	public static class FormatException extends RuntimeException {
		String _arg;
		public FormatException(String arg) {
			_arg = arg;
		}
		public String toString() { 
			return "incorrect parameter format: " + _arg;
		}
	}
	public static void addArgsToMap(String[] args, Map<String, Object> opts) {
		for (String a : args) {
			String[] parts = a.split("=", 2);
			if (parts.length > 1) {
				opts.put(parts[0], parts[1]);
			} else {
				throw new FormatException(a);
			}
		}
	}
	public static SortedMap<String, Object> parseArgs(String[] args) {
		SortedMap<String, Object> opts = new TreeMap<String, Object>();
		addArgsToMap(args, opts);
		return opts;
	}
}
