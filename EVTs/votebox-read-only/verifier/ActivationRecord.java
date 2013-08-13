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

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Set;

import verifier.value.*;
import verifier.ast.*;

import sexpression.*;

/**
 * An instance of this class represents a single record in the static chain
 * (which is a set of variable bindings). The environment is simply a chain of
 * these activation records (each which holds a set of bindings). The
 * environment is extended by chaning on a new activation record. Only the
 * evaluation of a let or a generic application (application of a nonprimitive
 * function to a set of arguments) can extend the environment. In the former
 * case, the environment will be extended so that the bindings introduced in the
 * let are accessible in the body of the let. In the latter case, the
 * environment will be extended such that the argument varibles are bound during
 * the execution of the lambda's body.
 * 
 * @author kyle
 */
public class ActivationRecord {

	/**
	 * This singleton marks the end of the chain. Perform an extend operation on
	 * this record in order to "create" an environment.
	 */
	public static final ActivationRecord END = new ActivationRecord(
			new HashMap<String, Value>(), null) {

		@Override
		public String toString() {
			return "";
		}

		@Override
		public Value lookup(String name) throws NotFoundException {
			if (_mappings.containsKey(name))
				return _mappings.get(name);
			throw new NotFoundException(name);
		}

		@Override
		public Set<String> keySet() {
			return _mappings.keySet();
		}

		@Override
		public HashMap<String, Value> extensions() {
			// Don't include the END bindings -- bindings is used
			return new HashMap<String, Value>();
		}
	};

	protected final HashMap<String, Value> _mappings;

	private final ActivationRecord _previous;

	private ActivationRecord(HashMap<String, Value> mappings,
			ActivationRecord previous) {
		_mappings = mappings;
		_previous = previous;
	}

	/**
	 * @param ase
	 *            Interpret this s-expression as an activation record and
	 *            construct a new activation record based on it.
	 */
	public ActivationRecord(ASExpression ase) {
		_previous = END;
		_mappings = new HashMap<String, Value>();

		for (ASExpression binding : (ListExpression) ase)
			_mappings.put(((ListExpression) binding).get(0).toString(),
					ASTParser.PARSER.parse(((ListExpression) binding).get(1))
							.eval(ActivationRecord.END));
	}

	/**
	 * @return This method returns the s-expression representation for this
	 *         record.
	 */
	public ASExpression toASE() {
		HashMap<String, Value> map = extensions();
		ArrayList<ASExpression> list = new ArrayList<ASExpression>(map.size());
		for (String s : map.keySet())
			list.add(new ListExpression(StringExpression.make(s), map.get(s)
					.toASE()));
		return new ListExpression(list);
	}

	/**
	 * Call this method from a plugin to redefine what mappings the base
	 * activation record uses. To change bindings in the non-initial activation
	 * record, use extend().
	 * 
	 * @param mappings
	 *            Set these mappings in the base activation record.
	 */
	public void setBindings(HashMap<String, Value> mappings) {
		if (this != END)
			throw new RuntimeException(
					"can only set the initial activation record.");
		_mappings.clear();
		_mappings.putAll(mappings);
	}

	/**
	 * Extend an environment (a chain of activation records) by adding a new set
	 * of bindings.
	 * 
	 * @param mappings
	 *            These are the bindings that will be added.
	 * @return This method returns a reference to the new head of the activation
	 *         record chain. This will be a newly allocated activation record
	 *         which is chained on top of the target record that this operation
	 *         was performed on.
	 */
	public ActivationRecord extend(HashMap<String, Value> mappings) {
		return new ActivationRecord(mappings, this);
	}

	/**
	 * Lookup a variable binding in the environment.
	 * 
	 * @param name
	 *            Lookup this identifier
	 * @return This method returns the value that the given identifer is bound
	 *         to.
	 * @throws NotFoundException
	 *             This method throws if the given variable is not bound in the
	 *             target environment.
	 */
	public Value lookup(String name) throws NotFoundException {
		if (_mappings.containsKey(name))
			return _mappings.get(name);
		return _previous.lookup(name);
	}

	/**
	 * @return This method returns a list of al the keys in this activation
	 *         record.
	 */
	public Set<String> keySet() {
		Set<String> belowset = _previous.keySet();
		belowset.addAll(_mappings.keySet());
		return belowset;
	}

	/**
	 * @return This method returns a mapping of all bindings in this activation
	 *         record and others higher up the static chain, excluding the top
	 *         (end) activation record. This value should not be viewed as a
	 *         representative collection of bindings -- this only contains the
	 *         extensions to the activation record. This is useful if you'd like
	 *         to serialize the activation record but leave out all the huge
	 *         values (like sets, dags) that every other node can independently
	 *         construct.
	 */
	protected HashMap<String, Value> extensions() {
		HashMap<String, Value> belowset = _previous.extensions();
		belowset.putAll(_mappings);
		return belowset;
	}

	/**
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		StringBuffer sb = new StringBuffer();
		for (String s : _mappings.keySet())
			sb.append("{" + s + " : " + _mappings.get(s) + "}");
		return _previous.toString() + sb.toString();
	}

	/**
	 * @see java.lang.Object#equals(java.lang.Object)
	 */
	@Override
	public boolean equals(Object o) {
		if (!(o instanceof ActivationRecord))
			return false;
		ActivationRecord oar = (ActivationRecord) o;

		Set<String> keys = keySet();
		for (String s : keys)
			if (!lookup(s).equals(oar.lookup(s)))
				return false;
		return true;
	}

}
