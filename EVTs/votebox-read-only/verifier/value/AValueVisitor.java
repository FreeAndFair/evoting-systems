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

package verifier.value;

import verifier.*;

public abstract class AValueVisitor implements IValueVisitor {

    public Value forExpression(Expression ase) {
        throw new UnexpectedTypeException( ase, "expression" );
    }

    public Value forFalse(False f) {
        throw new UnexpectedTypeException( f, "false value" );
    }

    public Value forInt(IntValue i) {
        throw new UnexpectedTypeException( i, "integer" );
    }

    public Value forSet(SetValue s) {
        throw new UnexpectedTypeException( s, "set" );
    }

    public Value forTrue(True t) {
        throw new UnexpectedTypeException( t, "true value" );
    }

    public Value forDAG(DAGValue d) {
        throw new UnexpectedTypeException( d, "dag value" );
    }

    public Value forReduction(Reduction ast) {
        throw new UnexpectedTypeException( ast, "ast value" );
    }
}
