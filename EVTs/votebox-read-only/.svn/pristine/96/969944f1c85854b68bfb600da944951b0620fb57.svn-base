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

package tap;

import java.util.regex.*;
import java.net.*;

public abstract class Access {
	@SuppressWarnings("serial")
	public static class InvalidHostPatternException extends Exception { }
	public static interface SocketRule {
		boolean permitted(Socket connection);
	}
	public static class Allow implements SocketRule {
		protected Pattern addressPattern = null;
		protected Pattern namePattern = null;
		public Allow(String patternStr) 
				throws InvalidHostPatternException
		{
			if (patternStr.matches("^[0-9]+\\.[0-9]+\\.[0-9]+\\.[0-9]+$")) {
				String[] bytes = patternStr.split("\\.");
				for (int i=0; i<4; i++) {
					if (bytes[i].equals("0") || bytes[i].equals("*")) {
						bytes[i] = "\\d+";
					}
				}
				addressPattern = Pattern.compile(
					"^" +
					bytes[0] + "\\." +
					bytes[1] + "\\." +
					bytes[2] + "\\." +
					bytes[3] +
					"$",
					Pattern.CASE_INSENSITIVE
				);
			} else if (patternStr.matches("^[-_a-zA-Z0-9.*]+$")) {
				namePattern = Pattern.compile(
					"^" +
					patternStr
						.replaceAll("\\.", "\\\\.")
						.replaceAll("\\*", ".*") +
					"$",
					Pattern.CASE_INSENSITIVE
				);
			} else {
				throw new InvalidHostPatternException();
			}
		}
		public boolean permitted(Socket connection) {
			InetAddress addr = connection.getInetAddress();
			if (addressPattern != null) {
				return addressPattern.matcher(
					addr.getHostAddress()).matches();
			} else {
				return namePattern.matcher(
					addr.getCanonicalHostName()).matches();
			}
		}
		public String toString() {
			return "Allow(" + (
				(addressPattern != null) 
					? ("ip=" + addressPattern.pattern())
					: ("host=" + namePattern.pattern())
			) + ")";
		}
	}
	public static class Deny extends Allow {
		public Deny(String patternStr) 
				throws InvalidHostPatternException
		{
			super(patternStr);
		}
		public boolean permitted(Socket connection) {
			return ! super.permitted(connection);
		}
		public String toString() {
			return "Deny(" + (
				(addressPattern != null) ? ("ip=" + addressPattern)
										 : ("host=" + namePattern)
			) + ")";
		}
	}
}

