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

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;

import sexpression.*;
import sexpression.stream.*;

import auditorium.*;

/**
 * Generate some test data.
 * 
 * @author kyle
 * 
 */
public class TestDataGen {

	// How many votes
	public static final int VOTES = 10000;
	public static final int INCREMENT = 50;
	
	// The next sequence number from each host
	private final int[] _sequence = new int[10];
	// The next nonce to be used for an authorize-to-cast
	private long _nonce;

	// Certificate and private key for each host
	private final Cert[] _cert = new Cert[10];
	private final Key[] _key = new Key[10];

	// Host pointer for each host.
	private final HostPointer[] _hp = new HostPointer[10];

	// The most recent Message
	private Message _recent;
	private ASEWriter _out;
	private FileOutputStream _stream;

	public void run() throws Exception {
		initHosts();
		initKeys();
		initLog(Integer.toString(INCREMENT));
		initSequence();

		int current = INCREMENT;
		_out.writeASE(makePollsOpen().toASE());
		for (int lcv = 0; lcv < VOTES; lcv++) {
			String str = Integer.toString((lcv % 9) + 1);
			_out.writeASE(makeAuth(str).toASE());
			_out.writeASE(makeCast(str).toASE());
			_out.writeASE(makeReceived(str).toASE());

			if (lcv == current) {
				current += INCREMENT;
				changeLog(Integer.toString(lcv), Integer.toString(current));
			}
		}
		_out.writeASE(makePollsClosed().toASE());
		_stream.close();
	}

	public void changeLog(String from, String to) throws Exception {
		_stream.flush();
		copy("testdata/" + from, "testdata/" + to);
		_out.writeASE(makePollsClosed().toASE());
		_stream.close();
		_stream = new FileOutputStream(new File("testdata/" + to), true);
		_out = new ASEWriter(_stream);
	}

	public Message makePollsOpen() throws Exception {
		return makeMessage(0, ASExpression.make("(polls-open 0 openkey)"), true);
	}

	public Message makePollsClosed() throws Exception {
		return makeMessage(0, ASExpression.make("(polls-closed 1)"), false);
	}

	public Message makeAuth(String to) throws Exception {
		return makeMessage(0, ASExpression.make("(authorized-to-cast " + to
				+ " " + Long.toString(_nonce) + " ballot)"), true);
	}

	public Message makeCast(String from) throws Exception {
		return makeMessage(Integer.parseInt(from), ASExpression
				.make("(cast-ballot " + Long.toString(_nonce)
						+ " encryptedballot)"), true);
	}

	public Message makeReceived(String to) throws Exception {
		Message msg = makeMessage(0, ASExpression.make("(ballot-received " + to
				+ " " + _nonce + ")"), true);
		_nonce++;
		return msg;
	}

	public Message makeMessage(int from, ASExpression message, boolean track)
			throws Exception {
		_sequence[from]++;
		Cert cert = _cert[from];
		Key key = _key[from];

		Signature sig;
		if (_recent != null) {
			sig = RSACrypto.SINGLETON.sign(new ListExpression(StringExpression
					.make("succeeds"), new ListExpression(new MessagePointer(
					_recent).toASE()), message), key);
		} else {
			sig = RSACrypto.SINGLETON.sign(new ListExpression(StringExpression
					.make("succeeds"), ListExpression.EMPTY, message), key);
		}

		Message msg = new Message("announce", _hp[from], Integer
				.toString(_sequence[from]), new ListExpression(StringExpression
				.make("signed-message"), cert.toASE(), sig.toASE()));
		if (track)
			_recent = msg;
		return msg;
	}

	public void initHosts() {
		for (int lcv = 0; lcv < 10; lcv++) {
			String lcvstr = Integer.toString(lcv);
			_hp[lcv] = new HostPointer(lcvstr, "192.168.1." + lcvstr, 9000);
		}
	}

	public void initLog(String runNum) {
		new File("testdata/").mkdir();
		_recent = null;
		try {
			_stream = new FileOutputStream(new File("testdata/" + runNum));
			_out = new ASEWriter(_stream);
		} catch (FileNotFoundException e) {
			throw new RuntimeException(e);
		}
	}

	public void initSequence() {
		// Sequence numbers initially zero
		for (int lcv = 0; lcv < 10; lcv++)
			_sequence[lcv] = -1;
		_nonce = -1;
	}

	public void initKeys() throws Exception {
		IKeyStore ks = new SimpleKeyStore("/keys");
		for (int lcv = 0; lcv < 10; lcv++) {
			_key[lcv] = ks.loadKey(Integer.toString(lcv));
			_cert[lcv] = ks.loadCert(Integer.toString(lcv));
		}
	}

	public static void copy(String from, String to) throws Exception {
		File inputFile = new File(from);
		File outputFile = new File(to);

		FileInputStream in = new FileInputStream(inputFile);
		FileOutputStream out = new FileOutputStream(outputFile);
		byte[] buffer = new byte[1024];
		int len;

		while ((len = in.read(buffer)) != -1)
			out.write(buffer, 0, len);

		in.close();
		out.close();
	}

	public static void main(String[] args) throws Exception {
		new TestDataGen().run();
	}
}
