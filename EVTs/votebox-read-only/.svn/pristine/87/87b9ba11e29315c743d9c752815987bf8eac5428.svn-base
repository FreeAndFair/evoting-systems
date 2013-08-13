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

package votebox.middle.view.test;

import java.net.URL;
import java.util.ArrayList;

import votebox.middle.IBallotVars;
import votebox.middle.Properties;
import votebox.middle.view.Layout;
import votebox.middle.view.LayoutParser;
import votebox.middle.view.RenderPage;
import votebox.middle.view.widget.Button;
import votebox.middle.view.widget.Label;
import votebox.middle.view.widget.ToggleButton;
import votebox.middle.view.widget.ToggleButtonGroup;
import junit.framework.TestCase;

public class LayoutParserTest extends TestCase {

	public final URL SCHEMA = getClass().getResource("/votebox/middle/schema/layout_schema.xsd");

	public static final String PATH = "votebox/middle/view/test/";

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
		vars.setLayoutFile(PATH + "test0");
		vars.setLayoutSchema(SCHEMA);
		Layout layout = new LayoutParser().getLayout( vars, 0, "en" );

		assertEquals(new ArrayList<RenderPage>(), layout.getPages());
		assertEquals(0, layout.getProperties().size());
	}

	/**
	 * Layout with two properties.
	 * 
	 * @throws Exception
	 */
	public void test_one() throws Exception {
		MyGlobalVars vars = new MyGlobalVars();
		vars.setLayoutFile(PATH + "test1");
		vars.setLayoutSchema(SCHEMA);
		Layout layout = new LayoutParser().getLayout(vars, 0, "en");

		assertEquals(new ArrayList<RenderPage>(), layout.getPages());

		Properties p = layout.getProperties();
		assertEquals(2, p.size());
		assertTrue(p.contains("LayoutProp1"));
		assertTrue(p.contains("LayoutProp2"));
		assertEquals(p.getString("LayoutProp1"), "1");
		assertEquals(p.getString("LayoutProp2"), "2");
	}

	/**
	 * Layout with one page.
	 * 
	 * @throws Exception
	 */
	public void test_two() throws Exception {
		MyGlobalVars vars = new MyGlobalVars();
		vars.setLayoutFile(PATH + "test2");
		vars.setLayoutSchema(SCHEMA);
		Layout layout = new LayoutParser().getLayout(vars, 0, "en");

		assertEquals(1, layout.getPages().size());
		assertEquals(0, layout.getPages().get(0).getChildren().size());
		assertEquals(0, layout.getProperties().size());
	}

	/**
	 * Layout with out page page has two labels
	 * 
	 * @throws Exception
	 */
	public void test_three() throws Exception {
		MyGlobalVars vars = new MyGlobalVars();
		vars.setLayoutFile(PATH + "test3");
		vars.setLayoutSchema(SCHEMA);
		Layout layout = new LayoutParser().getLayout(vars, 0, "en");

		assertEquals(1, layout.getPages().size());
		assertEquals(2, layout.getPages().get(0).getChildren().size());
		assertEquals(0, layout.getProperties().size());

		RenderPage rp = layout.getPages().get(0);
		Label l = (Label) rp.getChildren().get(0);
		assertEquals("one", l.getUniqueID());
		assertEquals(100, l.getX());
		assertEquals(101, l.getY());
		l = (Label) rp.getChildren().get(1);
		assertEquals("two", l.getUniqueID());
		assertEquals(200, l.getX());
		assertEquals(201, l.getY());
	}

	/**
	 * Layout with two page page one has two labels page two has one label
	 * 
	 * @throws Exception
	 */
	public void test_four() throws Exception {
		MyGlobalVars vars = new MyGlobalVars();
		vars.setLayoutFile(PATH + "test4");
		vars.setLayoutSchema(SCHEMA);
		Layout layout = new LayoutParser().getLayout(vars, 0, "en");

		assertEquals(2, layout.getPages().size());
		assertEquals(2, layout.getPages().get(0).getChildren().size());
		assertEquals(1, layout.getPages().get(1).getChildren().size());
		assertEquals(0, layout.getProperties().size());

		RenderPage rp = layout.getPages().get(0);
		Label l = (Label) rp.getChildren().get(0);
		assertEquals(0, l.getProperties().size());
		assertEquals("one", l.getUniqueID());
		assertEquals(100, l.getX());
		assertEquals(101, l.getY());
		l = (Label) rp.getChildren().get(1);
		assertEquals(0, l.getProperties().size());
		assertEquals("two", l.getUniqueID());
		assertEquals(200, l.getX());
		assertEquals(201, l.getY());

		rp = layout.getPages().get(1);
		l = (Label) rp.getChildren().get(0);
		assertEquals(0, l.getProperties().size());
		assertEquals("three", l.getUniqueID());
		assertEquals(300, l.getX());
		assertEquals(301, l.getY());
	}

	/**
	 * Layout with one page page has labels labels have properties.
	 */
	public void test_five() throws Exception {
		MyGlobalVars vars = new MyGlobalVars();
		vars.setLayoutFile(PATH + "test5");
		vars.setLayoutSchema(SCHEMA);
		Layout layout = new LayoutParser().getLayout(vars, 0, "en");

		assertEquals(1, layout.getPages().size());
		assertEquals(2, layout.getPages().get(0).getChildren().size());
		assertEquals(0, layout.getProperties().size());

		Properties p = layout.getPages().get(0).getChildren().get(0)
				.getProperties();
		assertTrue(layout.getPages().get(0).getChildren().get(0) instanceof Label);
		assertEquals(2, p.size());
		assertTrue(p.contains("OnePropOne"));
		assertEquals("property", p.getString("OnePropOne"));
		assertTrue(p.contains("OnePropTwo"));
		assertEquals("property", p.getString("OnePropTwo"));

		p = layout.getPages().get(0).getChildren().get(1).getProperties();
		assertEquals(1, p.size());
		assertTrue(p.contains("TwoPropOne"));
		assertEquals("property", p.getString("TwoPropOne"));
	}

	/**
	 * Layout with one page page has label and button label and button have
	 * properties
	 * 
	 * @throws Exception
	 */
	public void test_six() throws Exception {
		MyGlobalVars vars = new MyGlobalVars();
		vars.setLayoutFile(PATH + "test6");
		vars.setLayoutSchema(SCHEMA);
		Layout layout = new LayoutParser().getLayout(vars, 0, "en");

		assertEquals(1, layout.getPages().size());
		assertEquals(2, layout.getPages().get(0).getChildren().size());
		assertEquals(0, layout.getProperties().size());

		Label l = (Label) layout.getPages().get(0).getChildren().get(0);
		assertEquals("one", l.getUniqueID());
		assertEquals(100, l.getX());
		assertEquals(101, l.getY());
		Properties p = l.getProperties();
		assertEquals(2, p.size());
		assertTrue(p.contains("OnePropOne"));
		assertEquals("property", p.getString("OnePropOne"));
		assertTrue(p.contains("OnePropTwo"));
		assertEquals("property", p.getString("OnePropTwo"));

		Button b = (Button) layout.getPages().get(0).getChildren().get(1);
		assertEquals("two", b.getUniqueID());
		assertEquals(200, b.getX());
		assertEquals(201, b.getY());
		p = b.getProperties();
		assertEquals(1, p.size());
		assertTrue(p.contains("TwoPropOne"));
		assertEquals("property", p.getString("TwoPropOne"));
	}

	/**
	 * Layout with one page page has label, button, four toggle buttons, two in
	 * each of two groups. everything has properties except the page.
	 * 
	 * @throws Exception
	 */
	public void test_seven() throws Exception {
		MyGlobalVars vars = new MyGlobalVars();
		vars.setLayoutFile(PATH + "test7");
		vars.setLayoutSchema(SCHEMA);
		Layout layout = new LayoutParser().getLayout(vars, 0, "en");

		assertEquals(1, layout.getPages().size());
		assertEquals(6, layout.getPages().get(0).getChildren().size());
		assertEquals(0, layout.getProperties().size());

		Label l = (Label) layout.getPages().get(0).getChildren().get(0);
		assertEquals("one", l.getUniqueID());
		assertEquals(100, l.getX());
		assertEquals(101, l.getY());
		Properties p = l.getProperties();
		assertEquals(2, p.size());
		assertTrue(p.contains("OnePropOne"));
		assertEquals("property", p.getString("OnePropOne"));
		assertTrue(p.contains("OnePropTwo"));
		assertEquals("property", p.getString("OnePropTwo"));

		Button b = (Button) layout.getPages().get(0).getChildren().get(1);
		assertEquals("two", b.getUniqueID());
		assertEquals(200, b.getX());
		assertEquals(201, b.getY());
		p = b.getProperties();
		assertEquals(1, p.size());
		assertTrue(p.contains("TwoPropOne"));
		assertEquals("property", p.getString("TwoPropOne"));

		ToggleButton tb1 = (ToggleButton) layout.getPages().get(0).getChildren()
				.get(2);
		ToggleButtonGroup tb1g = tb1.getGroup();
		assertEquals("three", tb1.getUniqueID());
		assertEquals(300, tb1.getX());
		assertEquals(301, tb1.getY());
		p = tb1.getProperties();
		assertEquals(1, p.size());
		assertTrue(p.contains("ThreePropOne"));
		assertEquals("property", p.getString("ThreePropOne"));

		ToggleButton tb2 = (ToggleButton) layout.getPages().get(0).getChildren()
				.get(3);
		ToggleButtonGroup tb2g = tb2.getGroup();
		assertEquals("four", tb2.getUniqueID());
		assertEquals(400, tb2.getX());
		assertEquals(401, tb2.getY());
		p = tb2.getProperties();
		assertEquals(1, p.size());
		assertTrue(p.contains("FourPropOne"));
		assertEquals("property", p.getString("FourPropOne"));

		ToggleButton tb3 = (ToggleButton) layout.getPages().get(0).getChildren()
				.get(4);
		ToggleButtonGroup tb3g = tb3.getGroup();
		assertEquals("five", tb3.getUniqueID());
		assertEquals(500, tb3.getX());
		assertEquals(501, tb3.getY());
		p = tb3.getProperties();
		assertEquals(0, p.size());

		ToggleButton tb4 = (ToggleButton) layout.getPages().get(0).getChildren()
				.get(5);
		ToggleButtonGroup tb4g = tb4.getGroup();
		assertEquals("six", tb4.getUniqueID());
		assertEquals(600, tb4.getX());
		assertEquals(601, tb4.getY());
		p = tb4.getProperties();
		assertEquals(0, p.size());

		assertTrue(tb1g == tb2g);
		assertEquals(2, tb1g.getButtons().size());
		p = tb1g.getProperties();
		assertTrue(p.contains("GroupOneProperty"));
		assertEquals("property", p.getString("GroupOneProperty"));

		assertTrue(tb3g == tb4g);
		assertEquals(2, tb3g.getButtons().size());
		p = tb3g.getProperties();
		assertTrue(p.contains("GroupTwoProperty"));
		assertEquals("property", p.getString("GroupTwoProperty"));
	}

	/**
	 * For some reason, widgest from the entire layout are all getting thrown
	 * onto the first page. Is this the layout parser's fault ?
	 */
	public void test_eight() throws Exception {
		MyGlobalVars vars = new MyGlobalVars();
		vars.setLayoutFile(PATH + "test8");
		vars.setLayoutSchema(SCHEMA);
		Layout layout = new LayoutParser().getLayout(vars, 0, "en");

		assertEquals(2, layout.getPages().size());
		assertEquals(4, layout.getPages().get(0).getChildren().size());
		assertEquals(4, layout.getPages().get(1).getChildren().size());

		Label l = (Label) layout.getPages().get(0).getChildren().get(0);
		assertEquals("one", l.getUniqueID());

		Button b = (Button) layout.getPages().get(0).getChildren().get(1);
		assertEquals("two", b.getUniqueID());

		ToggleButton tb = (ToggleButton) layout.getPages().get(0).getChildren()
				.get(2);
		assertEquals("three", tb.getUniqueID());

		tb = (ToggleButton) layout.getPages().get(0).getChildren().get(3);
		assertEquals("four", tb.getUniqueID());

		l = (Label) layout.getPages().get(1).getChildren().get(0);
		assertEquals("five", l.getUniqueID());

		b = (Button) layout.getPages().get(1).getChildren().get(1);
		assertEquals("six", b.getUniqueID());

		tb = (ToggleButton) layout.getPages().get(1).getChildren().get(2);
		assertEquals("seven", tb.getUniqueID());
		
		tb = (ToggleButton) layout.getPages().get(1).getChildren().get(3);
		assertEquals("eight", tb.getUniqueID());
	}
	
	/**
	 * This is a ballot that was generated by the tool.
	 * @throws Exception
	 */
	public void test_nine() throws Exception {
		MyGlobalVars vars = new MyGlobalVars();
		vars.setLayoutFile(PATH + "test9");
		vars.setLayoutSchema(SCHEMA);
		Layout layout = new LayoutParser().getLayout(vars, 0, "en");
		
		assertEquals(4, layout.getPages().get(0).getChildren().size());
		assertEquals(5, layout.getPages().get(1).getChildren().size());
	}
}