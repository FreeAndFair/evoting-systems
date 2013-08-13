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

import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStreamReader;

import java.util.HashMap;

import sexpression.*;
import sexpression.parser.Parser;
import sexpression.lexer.Lexer;
import verifier.ast.*;
import verifier.value.Value;

/**
 * This is the top-level class for the generic s-expression rule verifier. Its
 * job, abstractly, is to interpret (in a programming language sense) a rule
 * (which is like a program). This rule should express some set of constraints,
 * meaning that the implicit semantics of this interpretation is a
 * "verification." This isn't required, however -- the verifier can evaluate
 * arbitrary expressions formed with the rules language (which is useful for
 * various tasks like searching the log for a message that matches a particular
 * pattern). In this way, the verifier acts more like a query tool than a
 * verifier.<br>
 * <br>
 * The verifier has two modes: it can either be used as a module for a larger
 * application, or it can run stand-alone. In the case where it runs as a
 * module, if the application using the verifier is log-generating in nature,
 * the verifier can incrementally evaluate the verification result of said
 * generated logs. The application can provide the verifier with incremental log
 * data and simply repeatedly ask the verifier to run. If the verifier can
 * produce a result with incomplete data, it will do so. If it cannot, it will
 * return a reduction of the problem (in effect -- a simpler rule which depends
 * only on the future data that is needed). This reduction will be expressed in
 * the rules language and returned as an AST<br>
 * <br>
 * The verifier is pluggable. This means that plugin writers are given the
 * ability to both define bindings for the initial activation record (global
 * variables) and new primitives (functions). Log data must be supplied to the
 * verifier via the plugin interface. This allows flexibility in log format and
 * allows for complete configurability over the API between the verifier and a
 * module using the verifier.
 * 
 * @see verifier.IVerifierPlugin
 * @see verifier.ast.IAST
 * @see verifier.ast.ASTParser
 * @author kyle
 * 
 */
public class Verifier {

	/**
	 * @return This method constructs and returns the collection of known
	 *         primitive AST fatories. This is currently used in place a
	 *         configuration file -- it is essentially the "list" of hard-wired
	 *         primitives. Others can, of course, be added via the plugin
	 *         interface.
	 */
	public static HashMap<String, ASTFactory> getPrimitives() {
		HashMap<String, ASTFactory> factories = new HashMap<String, ASTFactory>();

		factories.put(And.FACTORY.getName(), And.FACTORY);
		factories.put(Assert.FACTORY.getName(), Assert.FACTORY);
		factories.put(ListToSet.FACTORY.getName(), ListToSet.FACTORY);
		factories.put(SetToList.FACTORY.getName(), SetToList.FACTORY);
		factories.put(Equal.FACTORY.getName(), Equal.FACTORY);
		factories.put(Exists.FACTORY.getName(), Exists.FACTORY);
		factories.put(Exists.PFACTORY.getName(), Exists.PFACTORY);
		factories.put(Filter.FACTORY.getName(), Filter.FACTORY);
		factories.put(Forall.FACTORY.getName(), Forall.FACTORY);
		factories.put(Forall.PFACTORY.getName(), Forall.PFACTORY);
		factories.put(Greater.FACTORY.getName(), Greater.FACTORY);
		factories.put(GreaterEqual.FACTORY.getName(), GreaterEqual.FACTORY);
		factories.put(Impl.FACTORY.getName(), Impl.FACTORY);
		factories.put(Impl.AFACTORY.getName(), Impl.AFACTORY);
		factories.put(Impl.CFACTORY.getName(), Impl.CFACTORY);
		factories.put(Len.FACTORY.getName(), Len.FACTORY);
		factories.put(Less.FACTORY.getName(), Less.FACTORY);
		factories.put(LessEqual.FACTORY.getName(), LessEqual.FACTORY);
		factories.put(Let.FACTORY.getName(), Let.FACTORY);
		factories.put(Let.PFACTORY.getName(), Let.PFACTORY);
		factories.put(LetMatch.FACTORY.getName(), LetMatch.FACTORY);
		factories.put(LSpawn.FACTORY.getName(), LSpawn.FACTORY);
		factories.put(Num.FACTORY.getName(), Num.FACTORY);
		factories.put(Node.FACTORY.getName(), Node.FACTORY);
		factories.put(Not.FACTORY.getName(), Not.FACTORY);
		factories.put(Or.FACTORY.getName(), Or.FACTORY);
		factories.put(Quote.FACTORY.getName(), Quote.FACTORY);
		factories.put(Precedes.FACTORY.getName(), Precedes.FACTORY);
		factories.put(Spawn.FACTORY.getName(), Spawn.FACTORY);
		factories.put(Hash.FACTORY.getName(), Hash.FACTORY);
		factories.put(Get.FACTORY.getName(), Get.FACTORY);
		factories.put(Print.FACTORY.getName(), Print.FACTORY);
		factories.put(Red.FACTORY.getName(), Red.FACTORY);

		return factories;
	}

	/**
	 * @param args
	 *            Command line arguments constitute configuration parameters and
	 *            are of the form "var=val". This is the mechanism through
	 *            which the user supplies configuration parameters both to the
	 *            core verifier and to its plugins (A mapping of these
	 *            parameters is given to all plugin instances upon
	 *            construction). Variables that the core verifier will be
	 *            looking for include "rule", "config", "out".
	 */
	public static void main(String[] args) throws Exception {
		HashMap<String, String> argmap = new HashMap<String, String>();

		argmap = parseArgs(args);

		if (!argmap.containsKey("rule"))
			argNotFound("rule");
		if (!argmap.containsKey("log"))
			argNotFound("log");
		if (!argmap.containsKey("config"))
			argNotFound("config");

		ASExpression rule = readRule(argmap.get("rule"));
		String config = argmap.get("config");

		Verifier v = new Verifier(config, argmap);

		System.out.println("RESULT: " + v.eval(rule));
		System.out.println("ASSERTION FAILURES:");
		for (AssertionFailure f : Assert.FAILED_ASSERTIONS)
			System.out.println(f);
	}

	protected static void argNotFound(String arg) {
		System.err
				.println("Variable '"
						+ arg
						+ "' not specified. To specify a variable, pass '<var>=<val>' as a command line parameter>");
		System.exit(1);
	}

	protected static void argNotFormatted(String arg) {
		System.err
				.println("'"
						+ arg
						+ "' is not correct formatted. Correctly formatted arguments are of the form '<var>=<val>'. ");
		System.exit(1);
	}

	/**
	 * Read and parse the rule expression from a file.
	 * 
	 * @param rulelocation
	 *            Read the rule expression from this location.
	 * @return This method returns the s-expression representation of the rule.
	 * @throws FileNotFoundException
	 *             This method throws if the given location does not exist.
	 */
	public static ASExpression readRule(String rulelocation)
			throws FileNotFoundException {
		return new Parser(new Lexer(new InputStreamReader(new FileInputStream(
				new File(rulelocation))))).read();
	}

	/**
	 * Parse the command line arguments into a mapping. Arguments on the command
	 * line should be formatted '[var]=[val]'
	 * 
	 * @param args
	 *            This is the command line args.
	 * @return This method returns a mapping str->str which represents the
	 *         collection of '[var]=[val]' assignments from the command line.
	 */
	public static HashMap<String, String> parseArgs(String[] args) {
		HashMap<String, String> bindings = new HashMap<String, String>();
		for (String s : args) {
			String[] binding = s.split("=");
			if (binding.length != 2)
				argNotFormatted(s);
			binding[0] = binding[0].replaceAll(" ", "");
			binding[1] = binding[1].replaceAll(" ", "");
			bindings.put(binding[0], binding[1]);
		}
		return bindings;
	}

	private final HashMap<String, String> _args;
	private final HashMap<String, ASTFactory> _factories;

	/**
	 * Verifier's main should use this constructor.
	 * 
	 * @param args
	 *            This mapping represents the arguments that were passed to the
	 *            verifier on the command line. The elements of the map of the
	 *            form x->y appaer on the command line in the form x=y.
	 * @throws IOException
	 *             This method throws if there are IO errors reading the rule
	 *             file.
	 */
	private Verifier(String cfglocation, HashMap<String, String> args)
			throws InitException {
		_args = args;
		_factories = getPrimitives();

		loadPlugins(cfglocation);
	}

	/**
	 * An application wishing to use the verifier as a module should use this
	 * constructor or the Verifier(args) version.
	 */
	public Verifier() {
		_args = new HashMap<String, String>();
		_factories = getPrimitives();
	}

	/**
	 * An application wishing to use the verifier as a module should use this
	 * constructor.
	 */
	public Verifier(HashMap<String, String> args) {
		_args = args;
		_factories = getPrimitives();
	}

	/**
	 * Evaluate a particular rule.
	 * 
	 * @param rule
	 *            Parse and evaluate this s-expression using the base activation
	 *            record of the target verifier instance.
	 * @return This method returns the result of the evaluation.
	 */
	public Value eval(ASExpression rule) {
		Value v = new ASTParser(_factories, Constant.FACTORY).parse(rule).eval(
				ActivationRecord.END);
		Controller.SINGLETON.stop();
		LSpawn.POOL.stop();
		return v;
	}

	/**
	 * Evaluate a particular rule
	 * 
	 * @param rule
	 *            Evaluate this AST using the base activation record of the
	 *            target verifier instance.
	 * @return This method returns the result of the evaluation.
	 */
	public Value eval(AST rule) {
		Value v = rule.eval(ActivationRecord.END);
		Controller.SINGLETON.stop();
		LSpawn.POOL.stop();
		return v;
	}

	/**
	 * @return This method returns a map such that all mappings of the form x->y
	 *         were provided on the command line as 'x=y'.
	 */
	public HashMap<String, String> getArgs() {
		return _args;
	}

	/**
	 * @return This method returns the primitive factory registry. Add more
	 *         mappings to this in order to add new primitive operations.
	 */
	public HashMap<String, ASTFactory> getPrimitiveFactories() {
		return _factories;
	}

	private void loadPlugins(String cfglocation) throws InitException {
		// open the plugin list file.
		BufferedReader reader = null;
		try {
			reader = new BufferedReader(new InputStreamReader(
					new FileInputStream(new File(cfglocation))));
		} catch (FileNotFoundException e1) {
			System.err.println("Problem loading configuration file: " + e1);
			return;
		}

		// Read in plugin-constructed global values
		String s;
		try {
			while ((s = reader.readLine()) != null) {
				// Make sure blank lines don't screw us.
				s = s.replaceAll(" ", "");
				s = s.replaceAll("\n", "");
				if (s.equals(""))
					continue;

				// Load the class associated with the cfg entry.
				((IVerifierPlugin) Class.forName(s).newInstance()).init(this);
			}
		} catch (Exception e) {
			throw new InitException(e);
		}
	}
}
