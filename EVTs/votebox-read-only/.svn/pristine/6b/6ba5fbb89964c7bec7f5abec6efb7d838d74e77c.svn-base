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

package votebox.middle.ballot.test;

import java.net.URL;

import votebox.middle.IBallotVars;
import votebox.middle.ballot.Ballot;
import votebox.middle.ballot.BallotParser;

import junit.framework.TestCase;

/**
 * This JUnit test case is meant to test the functionality of the BallotParser
 * class.
 * 
 * @author derrley
 * 
 */
public class BallotParserTest extends TestCase {

	public final URL SCHEMA = getClass().getResource("/votebox/middle/schema/ballot_schema.xsd");

	public static final String PATH = "votebox/middle/ballot/test/";

	public class MyGlobalVars implements IBallotVars {

		private String _ballotPath;

		private String _ballotFile;

		private URL _ballotSchema;

		private String _layoutFile;

		private URL _layoutSchema;

		public String getBallotPath() {
			return _ballotPath;
		}

		public String getBallotFile() {
			return _ballotFile;
		}

		public URL getBallotSchema() {
			return _ballotSchema;
		}

		public String getLayoutFile() {
			return _layoutFile;
		}

		public URL getLayoutSchema() {
			return _layoutSchema;
		}

		public void setBallotPath(String string) {
			_ballotPath = string;
		}

		public void setBallotFile(String string) {
			_ballotFile = string;
		}

		public void setBallotSchema(URL string) {
			_ballotSchema = string;
		}

		public void setLayoutFile(String string) {
			_layoutFile = string;
		}

		public void setLayoutSchema(URL string) {
			_layoutSchema = string;
		}

	}

	/**
	 * Empty layout
	 * 
	 * @throws Exception
	 */
	public void test_zero() throws Exception {
		MyGlobalVars vars = new MyGlobalVars();
		vars.setBallotFile(PATH + "test1.xml");
		vars.setBallotSchema(SCHEMA);
		Ballot ballot = new BallotParser().getBallot(vars);

		assertEquals(1, ballot.getCards().size());
		assertEquals(ballot, ballot.getCards().get(0).getParent());
		assertTrue(ballot.getProperties().contains("prop1"));
		assertTrue(ballot.getCards().get(0).getProperties().contains("prop2"));
	}
}
