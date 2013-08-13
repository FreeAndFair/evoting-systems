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

package verifier.ast.test;

import static org.junit.Assert.*;

import org.junit.Test;

import verifier.*;
import verifier.value.*;
import verifier.ast.*;

import sexpression.*;

/**
 * These test represent situations where the world is "closed" (every value in
 * the system is sealed).
 * 
 * @author kyle
 * 
 */
public class ClosedWorldTests {

	private final ASTParser _parser;

	public ClosedWorldTests() {
		_parser = new ASTParser(Verifier.getPrimitives(), Constant.FACTORY);
	}

	private Value test(String expression) {
		return _parser.parse(expression).eval(ActivationRecord.END);
	}

	// ** Constants
	@Test
	public void constants_truth() {
		assertEquals(True.SINGLETON, test("true"));
		assertEquals(False.SINGLETON, test("false"));
	}

	@Test
	public void constants_int() {
		assertEquals(new IntValue(0), test("0"));
		assertEquals(new IntValue(41), test("41"));
		assertEquals(new IntValue(-124), test("-124"));
	}

	@Test
	public void constants_expression() {
		assertEquals(new Expression(ASExpression.make("hello")),
				test("(quote hello)"));
		assertEquals(new Expression(ASExpression.make("(hello hi)")),
				test("(quote (hello hi))"));
		assertEquals(new Expression(ASExpression.make("#any")),
				test("(quote #any)"));
	}

	@Test
	public void constants_set() {
		Expression[] set = new Expression[2];
		set[0] = new Expression(ASExpression.make("hello"));
		set[1] = new Expression(ASExpression.make("hi"));
		assertEquals(new SetValue(set), test("(list->set (quote (hello hi)))"));
	}

	// ** Connectives
	@Test
	public void connectives_and() {
		assertEquals(True.SINGLETON, test("(and (true true true))"));
		assertEquals(False.SINGLETON, test("(and (false true true))"));
		assertEquals(False.SINGLETON, test("(and (true true false))"));
		assertEquals(False.SINGLETON, test("(and (true false false))"));
		assertEquals(False.SINGLETON, test("(and (false false false))"));
	}

	@Test(expected = UnexpectedTypeException.class)
	public void connectives_and_fail_num() {
		test("(and (1))");
	}

	@Test(expected = UnexpectedTypeException.class)
	public void connectives_and_fail_exp() {
		test("(and ((quote 1)))");
	}

	@Test(expected = UnexpectedTypeException.class)
	public void connectives_and_fail_set() {
		test("(and ((list->set (quote (1)))))");
	}

	@Test
	public void connectives_or() {
		assertEquals(True.SINGLETON, test("(or (true true true))"));
		assertEquals(True.SINGLETON, test("(or (false true true))"));
		assertEquals(True.SINGLETON, test("(or (true true false))"));
		assertEquals(True.SINGLETON, test("(or (true false false))"));
		assertEquals(False.SINGLETON, test("(or (false false false))"));
	}

	@Test(expected = UnexpectedTypeException.class)
	public void connectives_or_fail_num() {
		test("(or (1))");
	}

	@Test(expected = UnexpectedTypeException.class)
	public void connectives_or_fail_exp() {
		test("(or ((quote 1)))");
	}

	@Test(expected = UnexpectedTypeException.class)
	public void connectives_or_fail_set() {
		test("(or ((list->set (quote (1)))))");
	}

	@Test
	public void connectives_not() {
		assertEquals(False.SINGLETON, test("(not true)"));
		assertEquals(True.SINGLETON, test("(not false)"));
	}

	@Test(expected = UnexpectedTypeException.class)
	public void connectives_not_fail_num() {
		test("(not 1)");
	}

	@Test(expected = UnexpectedTypeException.class)
	public void connectives_not_fail_exp() {
		test("(not (quote 1))");
	}

	@Test(expected = UnexpectedTypeException.class)
	public void connectives_not_fail_set() {
		test("(not (list->set (quote (1))))");
	}

	@Test
	public void connectives_impl() {
		assertEquals(True.SINGLETON, test("(impl true true)"));
		assertEquals(False.SINGLETON, test("(impl true false)"));
		assertEquals(True.SINGLETON, test("(impl false true)"));
		assertEquals(True.SINGLETON, test("(impl false false)"));
	}

	@Test(expected = UnexpectedTypeException.class)
	public void connectives_impl_fail_num() {
		test("(impl 1 2)");
	}

	@Test(expected = UnexpectedTypeException.class)
	public void connectives_impl_fail_exp() {
		test("(impl (quote 1) (quote 2))");
	}

	@Test(expected = UnexpectedTypeException.class)
	public void connectives_impl_fail_set() {
		test("(impl (list->set (quote (1))) (list->set (quote (2))))");
	}

	// ** Quantifiers
	@Test
	public void quantifiers_exists() {
		assertEquals(True.SINGLETON,
				test("(exists x (list->set (quote (1 2 3))) (= x (quote 1)))"));
		assertEquals(True.SINGLETON,
				test("(exists x (list->set (quote (1 2 3))) (= x (quote 2)))"));
		assertEquals(True.SINGLETON,
				test("(exists x (list->set (quote (1 2 3))) (= x (quote 3)))"));
		assertEquals(False.SINGLETON,
				test("(exists x (list->set (quote (1 2 3))) (= x (quote 4)))"));
	}

	@Test
	public void quantifiers_forall() {
		assertEquals(False.SINGLETON,
				test("(forall x (list->set (quote (1 2 3))) (= x (quote 1)))"));
		assertEquals(False.SINGLETON,
				test("(forall x (list->set (quote (1 2 3))) (= x (quote 2)))"));
		assertEquals(False.SINGLETON,
				test("(forall x (list->set (quote (1 2 3))) (= x (quote 3)))"));
		assertEquals(False.SINGLETON,
				test("(forall x (list->set (quote (1 2 3))) (= x (quote 4)))"));

		assertEquals(
				True.SINGLETON,
				test("(forall x (list->set (quote (1 2 3))) (< (string->num x) 4))"));

		assertEquals(True.SINGLETON,
				test("(forall x (list->set (quote (2 2 2))) (= x (quote 2)))"));
		assertEquals(
				True.SINGLETON,
				test("(forall x (list->set (quote (2 2 2))) (= (string->num x) 2))"));

	}

	// Functions
	@Test
	public void functions_filter() {
		assertEquals(test("(list->set (quote ()))"),
				test("(filter (list->set (quote ())) (quote #any))"));
		assertEquals(test("(list->set (quote ()))"),
				test("(filter (list->set (quote (hi))) (quote hey))"));
		assertEquals(test("(list->set (quote (hi)))"),
				test("(filter (list->set (quote (hi))) (quote hi))"));
		assertEquals(
				test("(list->set (quote ((how) (you))))"),
				test("(filter (list->set (quote (hi (how) are (you)))) (quote #list:#any))"));
	}

	// Predicates
	@Test
	public void predicates_less() {
		assertEquals(True.SINGLETON, test("(< 0 1)"));
		assertEquals(True.SINGLETON, test("(< -1 0)"));
		assertEquals(False.SINGLETON, test("(< 0 0)"));
		assertEquals(False.SINGLETON, test("(< 1 0)"));
	}

	@Test(expected = UnexpectedTypeException.class)
	public void predicates_less_fail_exp() {
		test("(< (quote 1) (quote 2))");
	}

	@Test(expected = UnexpectedTypeException.class)
	public void predicates_less_fail_set() {
		test("(< (list->set (quote 1)) (list->set (quote 2)))");
	}

	@Test(expected = UnexpectedTypeException.class)
	public void predicates_less_fail_truth() {
		test("(< true false)");
	}

	@Test
	public void predicates_lesseq() {
		assertEquals(True.SINGLETON, test("(<= 0 1)"));
		assertEquals(True.SINGLETON, test("(<= -1 0)"));
		assertEquals(True.SINGLETON, test("(<= 0 0)"));
		assertEquals(False.SINGLETON, test("(<= 1 0)"));
	}

	@Test(expected = UnexpectedTypeException.class)
	public void predicates_lesseq_fail_exp() {
		test("(<= (quote 1) (quote 2))");
	}

	@Test(expected = UnexpectedTypeException.class)
	public void predicates_lesseq_fail_set() {
		test("(<= (list->set (quote 1)) (list->set (quote 2)))");
	}

	@Test(expected = UnexpectedTypeException.class)
	public void predicates_lesseq_fail_truth() {
		test("(<= true false)");
	}

	@Test
	public void predicates_greater() {
		assertEquals(False.SINGLETON, test("(> 0 1)"));
		assertEquals(False.SINGLETON, test("(> -1 0)"));
		assertEquals(False.SINGLETON, test("(> 0 0)"));
		assertEquals(True.SINGLETON, test("(> 1 0)"));
	}

	@Test(expected = UnexpectedTypeException.class)
	public void predicates_greater_fail_exp() {
		test("(> (quote 1) (quote 2))");
	}

	@Test(expected = UnexpectedTypeException.class)
	public void predicates_greater_fail_set() {
		test("(> (list->set (quote 1)) (list->set (quote 2)))");
	}

	@Test(expected = UnexpectedTypeException.class)
	public void predicates_greater_fail_truth() {
		test("(> true false)");
	}

	@Test
	public void predicates_greatereq() {
		assertEquals(False.SINGLETON, test("(>= 0 1)"));
		assertEquals(False.SINGLETON, test("(>= -1 0)"));
		assertEquals(True.SINGLETON, test("(>= 0 0)"));
		assertEquals(True.SINGLETON, test("(>= 1 0)"));
	}

	@Test(expected = UnexpectedTypeException.class)
	public void predicates_greatereq_fail_exp() {
		test("(>= (quote 1) (quote 2))");
	}

	@Test(expected = UnexpectedTypeException.class)
	public void predicates_greatereq_fail_set() {
		test("(>= (list->set (quote 1)) (list->set (quote 2)))");
	}

	@Test(expected = UnexpectedTypeException.class)
	public void predicates_greatereq_fail_truth() {
		test("(>= true false)");
	}

	@Test
	public void predicates_equal() {
		// numbers
		assertEquals(False.SINGLETON, test("(= 0 1)"));
		assertEquals(False.SINGLETON, test("(= -1 0)"));
		assertEquals(True.SINGLETON, test("(= 0 0)"));
		assertEquals(True.SINGLETON, test("(= -1 -1)"));
		assertEquals(False.SINGLETON, test("(= 1 0)"));

		// expressions
		assertEquals(True.SINGLETON, test("(= (quote hi) (quote hi))"));
		assertEquals(False.SINGLETON, test("(= (quote hi) (quote ho))"));
		assertEquals(False.SINGLETON, test("(= (quote (1 2)) (quote (2 1)))"));
		assertEquals(True.SINGLETON, test("(= (quote (1 2)) (quote (1 2)))"));

		// sets
		assertEquals(True.SINGLETON,
				test("(= (list->set (quote (1 2))) (list->set (quote (2 1))))"));
		assertEquals(True.SINGLETON,
				test("(= (list->set (quote (1 2))) (list->set (quote (1 2))))"));
		assertEquals(
				True.SINGLETON,
				test("(= (list->set (quote (hi how are you?))) (list->set (quote (you? are hi how))))"));
		assertEquals(
				False.SINGLETON,
				test("(= (list->set (quote (hi how are you?))) (list->set (quote (you? are hai how))))"));

		// truth
		assertEquals(True.SINGLETON, test("(= true true)"));
		assertEquals(True.SINGLETON, test("(= false false)"));
		assertEquals(False.SINGLETON, test("(= false true)"));
		assertEquals(False.SINGLETON, test("(= true false)"));
	}

	// ** functions
	@Test
	public void filter() {
		assertEquals(test("(list->set (quote ()))"),
				test("(filter (list->set (quote ())) (quote #any))"));
		assertEquals(
				test("(list->set (quote ()))"),
				test("(filter (list->set (quote ((hi) (kyle)))) (quote #string))"));
		assertEquals(
				test("(list->set (quote (hi)))"),
				test("(filter (list->set (quote (how hi are you))) (quote hi))"));
		assertEquals(
				test("(list->set (quote ((what is) (up with))))"),
				test("(filter (list->set (quote ((what is) (up with) you))) (quote #list:#string))"));
	}

	@Test(expected = UnexpectedTypeException.class)
	public void filter_fail_num_left() {
		test("(filter 5 (quote hi))");
	}

	@Test(expected = UnexpectedTypeException.class)
	public void filter_fail_num_right() {
		test("(filter (list->set (quote (hi))) 5)");
	}

	@Test(expected = UnexpectedTypeException.class)
	public void filter_fail_list_left() {
		test("(filter (quote hi) (quote hi))");
	}

	@Test(expected = UnexpectedTypeException.class)
	public void filter_fail_set_right() {
		test("(filter (list->set (quote (hi))) (list->set (quote hi)))");
	}

	/*@Test(expected = UnexpectedTypeException.class)
	public void filter_fail_lambda_left() {
		test("(filter (lambda (x) x) (quote hi))");
	}*/

	/*@Test(expected = UnexpectedTypeException.class)
	public void filter_fail_lambda_right() {
		test("(filter (list->set (quote (hi))) (lambda (x) x))");
	}*/

	@Test(expected = UnexpectedTypeException.class)
	public void filter_fail_true_left() {
		test("(filter true (quote hi))");
	}

	@Test(expected = UnexpectedTypeException.class)
	public void filter_fail_false_right() {
		test("(filter (list->set (quote (hi))) false)");
	}

	@Test
	public void get() {
		assertEquals(test("(quote hi)"),
				test("(get 0 (quote (hi (how) are you)))"));
		assertEquals(test("(quote (how))"),
				test("(get 1 (quote (hi (how) are you)))"));
		assertEquals(test("(quote are)"),
				test("(get 2 (quote (hi (how) are you)))"));
	}

	@Test(expected = IndexException.class)
	public void get_bounds_lower() {
		test("(get -1 (quote (hi)))");
	}

	@Test(expected = IndexException.class)
	public void get_bounds_upper() {
		test("(get 1 (quote (hi)))");
	}

	@Test(expected = UnexpectedTypeException.class)
	public void get_string() {
		test("(get 0 (quote hi))");
	}

	@Test(expected = UnexpectedTypeException.class)
	public void get_set() {
		test("(get 0 (list->set (quote (hi))))");
	}

	@Test(expected = UnexpectedTypeException.class)
	public void get_num() {
		test("(get 0 5)");
	}

	/*@Test(expected = UnexpectedTypeException.class)
	public void get_lambda() {
		test("(get 0 (lambda (x) x))");
	}*/

	@Test(expected = UnexpectedTypeException.class)
	public void get_true() {
		test("(get 0 true)");
	}

	@Test(expected = UnexpectedTypeException.class)
	public void get_left_string() {
		test("(get (quote hi) (quote (hi)))");
	}

	@Test(expected = UnexpectedTypeException.class)
	public void get_left_list() {
		test("(get (quote (hi)) (quote (hi)))");
	}

	@Test(expected = UnexpectedTypeException.class)
	public void get_left_set() {
		test("(get (list->set (quote (hi))) (quote (hi)))");
	}

	/*@Test(expected = UnexpectedTypeException.class)
	public void get_left_lambda() {
		test("(get (lambda (x) x) (quote (hi)))");
	}*/

	@Test(expected = UnexpectedTypeException.class)
	public void get_left_true() {
		test("(get true (quote (hi)))");
	}

	@Test
	public void hash() {
		assertEquals(new Expression(StringExpression
				.makeString(StringExpression.make("hi").getSHA1())),
				test("(hash (quote hi))"));
		assertEquals(new Expression(StringExpression
				.makeString(new ListExpression("hey", "you").getSHA1())),
				test("(hash (quote (hey you)))"));
	}

	@Test(expected = UnexpectedTypeException.class)
	public void hash_set() {
		test("(hash (list->set (quote (hi))))");
	}

	@Test(expected = UnexpectedTypeException.class)
	public void hash_num() {
		test("(hash 5)");
	}

	/*@Test(expected = UnexpectedTypeException.class)
	public void hash_lambda() {
		test("(hash (lambda (x) x))");
	}*/

	@Test(expected = UnexpectedTypeException.class)
	public void hash_true() {
		test("(hash true)");
	}

	// ** let- match
	@Test
	public void letmatch() {
		assertEquals(True.SINGLETON,
				test("(let-match (quote (1 2 3)) (quote (1 2 3)) true false)"));
		assertEquals(
				test("(quote (1 2 3))"),
				test("(let-match (quote %kyle:#list:#any) (quote (1 2 3)) kyle false)"));
	}

	@Test(expected = UnexpectedTypeException.class)
	public void letmatch_fail_num_1() {
		test("(let-match 1 (quote 1) 1 2)");
	}

	@Test(expected = UnexpectedTypeException.class)
	public void letmatch_fail_num_2() {
		test("(let-match (quote 1) 1 1 2)");
	}

	@Test(expected = UnexpectedTypeException.class)
	public void letmatch_fail_set_1() {
		test("(let-match 1 (list->set (quote 1)) 1 2)");
	}

	// ** let
	/*@Test
	public void let() {
		assertEquals(new IntValue(5), test("(let () 5)"));
		assertEquals(new IntValue(5), test("(let ((x 5)) x)"));
		assertEquals(new IntValue(5), test("(let ((x 2)(y 3)) (+ x y))"));
		assertEquals(new IntValue(5),
				test("(let ((x (quote #any))) (let-match x (quote hi) 5 4))"));
	}*/

	// ** application
	/*@Test
	public void application() {
		assertEquals(new IntValue(5),
				test("(let ((blah (lambda (x) (+ x 1)))) (blah 4))"));
		assertEquals(new IntValue(5), test("(let "
				+ "((blah (lambda (x) (+ x 1)))"
				+ "(blah+blah (lambda (x y) (+ x y)))"
				+ " (blah (blah+blah 2 2))))"));

	}*/

	// ** assert
	@Test
	public void assert_() {
		assertEquals(
				False.SINGLETON,
				test("(forall x (list->set (quote (1 2 3 4))) (assert EQUALS_3 true (= (string->num x) 3)))"));
		for (AssertionFailure f : Assert.FAILED_ASSERTIONS)
			System.err.println(f);

	}
}
