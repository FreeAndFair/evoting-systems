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

package verifier.ast;

import java.io.EOFException;
import java.io.IOException;
import java.net.ServerSocket;
import java.net.Socket;
import java.net.SocketException;

import sexpression.*;
import sexpression.stream.*;
import verifier.*;
import verifier.task.*;
import verifier.value.*;

public class Node extends AST {

	public static int PORT = 9001;
	public static int NUM_THREADS = 2;
	public static final ASTFactory FACTORY = new ASTFactory() {

		@Override
		public String getName() {
			return "node";
		}

		@Override
		public String getPattern() {
			return "(node)";
		}

		@Override
		public AST make(ASExpression from, ListExpression matchresult,
				ASTParser parser) {
			return new Node();
		}
	};

	private Pool _pool;
	private ServerSocket _server;

	private Node() {
		super(null);
	}

	@Override
	public Value eval(ActivationRecord environment) {
		_pool = new Pool(NUM_THREADS);
		_pool.start();
		try {
			_server = new ServerSocket(PORT);
			try {

				Socket s = _server.accept();
				ASEInputStreamReader reader = new ASEInputStreamReader(s
						.getInputStream());
				try {
					while (true) {
						ASExpression ase = reader.read();
						Task t = new Task(ase);
						t.setOutbound(s.getOutputStream());
						_pool.run(t);
					}
				} catch (EOFException e) {}
				System.err.println();

			} catch (SocketException e) {} catch (IOException e) {
				throw new RuntimeException(e);
			} catch (InvalidVerbatimStreamException e) {
				throw new RuntimeException(e);
			}

		} catch (IOException e) {
			throw new RuntimeException(e);
		}
		_pool.stop();
		return False.SINGLETON;
	}
}
