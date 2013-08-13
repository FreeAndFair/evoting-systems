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

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.net.Socket;
import java.util.ArrayList;

import sexpression.*;
import sexpression.stream.*;
import verifier.ast.*;
import verifier.task.Barrier;
import verifier.value.*;

public class Controller {

	public static final String[] HOSTS = { "sysrack02", "sysrack03", "sysrack04", "sysrack05",
			"sysrack06" };
	public static final Controller SINGLETON = new Controller();

	private Controller() {
		_out = new ArrayList<OutputStream>();
		_sockets = new ArrayList<Socket>();
	}

	private final ArrayList<OutputStream> _out;
	private final ArrayList<Socket> _sockets;
	private int _num;
	private boolean _running = false;

	private void start() {
		_num = 0;
		_running = true;

		_out.clear();
		_sockets.clear();

		final Barrier b = new Barrier(HOSTS.length + 1);

		for (String s : HOSTS) {
			try {
				final String fs = s;
				final Socket socket = new Socket(s, Node.PORT);
				final OutputStream os = socket.getOutputStream();
				final InputStream is = socket.getInputStream();
				_sockets.add(socket);
				_out.add(os);
				new Thread(new Runnable() {

					public void run() {
						b.hit();
						thread(is, fs);
					}
				}).start();
			} catch (IOException e) {
				throw new RuntimeException(e);
			}

		}
		b.hit();
	}

	public void stop() {
		_running = false;
		try {
			for (Socket s : _sockets)
				s.close();
		} catch (IOException e) {
			throw new RuntimeException(e);
		}
	}

	public OutputStream getOutbound() {
		if (!_running)
			start();

		if (_out.size() == 0)
			throw new RuntimeException("no connections!");

		if (_num == _out.size())
			_num = 0;
		OutputStream ret = _out.get(_num);
		_num++;
		return ret;
	}

	private void thread(InputStream is, String id) {
		ASTParser parser = new ASTParser(Verifier.getPrimitives(),
				Constant.FACTORY);
		try {
			while (_running) {
				ListExpression list = (ListExpression) new ASEInputStreamReader(
						is).read();
				Value v = parser.parse(list.get(1)).eval(ActivationRecord.END);
				Future.fromID(Long.parseLong(list.get(0).toString()))
						.realize(v);
			}
		} catch (IOException e) {
			if (_running)
				throw new RuntimeException(e);
		} catch (InvalidVerbatimStreamException e) {
			throw new RuntimeException(e);
		}
	}
}
