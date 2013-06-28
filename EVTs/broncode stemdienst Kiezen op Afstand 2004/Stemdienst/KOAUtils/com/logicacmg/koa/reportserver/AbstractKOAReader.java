/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.reportserver.AbstractKOAReader.java
  *
  * -----------------------------------------------------------------------
  * 
  *  (c) 2003  Ministerie van Binnenlandse Zaken en Koninkrijkrelaties
  *
  *  Project		: Kiezen Op Afstand (KOA)
  *  Project Number	: ECF-2651
  *  
  *  History:
  *  Version	Date		Name		Reason
  * ---------------------------------------------------------
  *  0.1		15-05-2003	MKu			First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.reportserver;
import java.io.IOException;
import java.io.Reader;

import com.logicacmg.koa.utils.KOALogHelper;
/**
 * Abstract class to implement the common read functionallity
 * for all readers.
 * 
 * @author KuijerM
 */
public abstract class AbstractKOAReader extends Reader
{
	protected StringBuffer sBuffer = new StringBuffer();
	/**
	 * @see java.io.Reader#read(char[], int, int)
	 */
	public int read(char[] carray, int offset, int len) throws IOException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[AbstractKOAReader.read] reading more characters...");
		/* see if we can get this amount of characters */
		String add = getMore(len - sBuffer.length());
		/* add the new string to the buffer */
		if (add != null)
		{
			sBuffer.append(add);
		}
		int retval = -1;
		/* check if there is content in the buffer */
		if (sBuffer.length() == 0)
		{
			retval = -1;
		}
		else if (len > sBuffer.length())
		{
			/* offset smaller than length */
			sBuffer.getChars(0, sBuffer.length(), carray, offset);
			retval = sBuffer.length();
			sBuffer.delete(0, sBuffer.length());
		}
		else
		{
			sBuffer.getChars(0, len, carray, offset);
			retval = len;
			sBuffer.delete(0, len);
		}
		return retval;
	}
	/**
	 * Abstract method to get more data
	 * Must be implemented by all subclasses.
	 * 
	 * @param blocksize The blocksize that the retuning String should be
	 * 
	 * @return The String with the minimum length of the block size
	 */
	protected abstract String getMore(int blocksize);
	/**
	 * Abstract method to close the reader.
	 * Must be implemented by all subclasses
	 * 
	 * @throws IOException Exception when something goes wrong while closing the Reader
	 */
	public abstract void close() throws IOException;
}