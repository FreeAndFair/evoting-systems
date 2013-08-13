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

package votebox.auditoriumverifierplugins;

import auditorium.*;
import sexpression.*;
import verifier.*;
import verifier.ast.*;
import verifier.value.*;

public class SignatureVerify extends AST {

	public static final ASTFactory FACTORY = new PrimFactory(2,
			new IConstructor() {

				public AST make(ASExpression from, AST... args) {
					return new SignatureVerify(from, args[0], args[1]);
				}
			}) {

		@Override
		public String getName() {
			return "signature-verify";
		}
	};

	private final AST _cert;
	private final AST _signature;

	private SignatureVerify(ASExpression from, AST cert, AST signature) {
		super(from);
		_cert = cert;
		_signature = signature;
	}

	@Override
	public Value eval(ActivationRecord environment) {
		final Value cert = _cert.eval(environment);
		final Value sig = _signature.eval(environment);

		return cert.execute(new AValueVisitor() {

			@Override
			public Value forExpression(final Expression certvalue) {
				return sig.execute(new AValueVisitor() {

					@Override
					public Value forExpression(Expression sigvalue) {
						try {
							Cert c = new Cert(certvalue.getASE());
							Signature s = new Signature(sigvalue.getASE());
							RSACrypto.SINGLETON.verify(s, c);
							return True.SINGLETON;
						} catch (IncorrectFormatException e) {
							return False.SINGLETON;
						} catch (AuditoriumCryptoException e) {
							return False.SINGLETON;
						}
					}
				});
			}
		});
	}
}
