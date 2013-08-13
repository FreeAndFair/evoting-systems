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

package tap;

import java.util.LinkedList;
import java.util.Iterator;

public class ByteArrayBuffer implements Cloneable {
	protected LinkedList<byte[]> list;
	protected int length;
	protected boolean flat;
	
	public ByteArrayBuffer() {
		list = new LinkedList<byte[]>();
		length = 0;
		flat = true;
	}

	public ByteArrayBuffer(byte[] array) {
		list = new LinkedList<byte[]>();
		length = 1;
		flat = true;
		
		list.add(array);
	}
	
	public Object clone() {
		return new ByteArrayBuffer(toByteArray());
	}

	public int length() {
		return this.length;
	}

	public byte[] toByteArray() {
		flatten();
		if (length == 0) return new byte[0];
		return list.getFirst();
	}
	
	public synchronized void flatten() {
		if (flat) return;
		
		byte[] newBuf = new byte[length];
		int p = 0;
		for (Iterator i = list.iterator(); i.hasNext(); ) {
			byte[] bi = (byte[])(i.next());
			System.arraycopy(bi, 0, newBuf, p, bi.length);
			p += bi.length;
		}
		
		list.clear();
		list.add(newBuf);
		flat = true;
	}
	
	public void attach(byte[] buf) {
		if (buf.length == 0) return;
		
		flat = flat && (length == 0); // it's still flat after the first append()

		list.add(buf);
		length += buf.length;
	}

	public void append(byte[] buf, int bufStart, int bufLen) {
		if (bufLen == 0) return;

		byte[] slice = new byte[bufLen];
		System.arraycopy(buf, bufStart, slice, 0, bufLen);

		attach(slice);
	}
	
	public void append(byte[] buf) {
		append(buf, 0, buf.length);
	}
	
	public String toString() {
		String s;
		byte[] buf = toByteArray();
		
		flatten();
		if (length < 22) s = new String(buf);
		else {
			byte[] prefix = new byte[10];
			byte[] suffix = new byte[10];
			System.arraycopy(buf, 0, prefix, 0, 10);
			System.arraycopy(buf, length-11, suffix, 0, 10);
			s = new String(prefix) + ".." + new String(suffix);
		}
		
		return "<ByteArrayBuffer [" + s + "] len=" + length + ">";
	}
}