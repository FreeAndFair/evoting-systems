// Reversed by Rick using JAD decompiler with some tweaks
// Jad home page: http://www.geocities.com/kpdus/jad.html
// Decompiler options: packimports(3) 
// Source File Name:   BasicException.java

package org.scantegrity.common.ballotstandards.basic.exceptions;

import java.io.Serializable;

public class BasicException extends Exception
    implements Serializable
{

    /**
	 * 
	 */
	private static final long serialVersionUID = -8623002837846693386L;

	public BasicException()
    {
    }

    public BasicException(String text)
    {
        super(text);
    }

    public BasicException(Exception e)
    {
        super(e);
    }
}
