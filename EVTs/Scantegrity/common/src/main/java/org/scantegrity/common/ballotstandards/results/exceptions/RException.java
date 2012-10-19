// Reversed by Rick using JAD decompiler with some tweaks
// Jad home page: http://www.geocities.com/kpdus/jad.html
// Decompiler options: packimports(3) 
// Source File Name:   RException.java

package org.scantegrity.common.ballotstandards.results.exceptions;

import java.io.Serializable;

public class RException extends Exception
    implements Serializable
{

    /**
	 * 
	 */
	private static final long serialVersionUID = 1271564667912017256L;

	public RException()
    {
    }

    public RException(String text)
    {
        super(text);
    }

    public RException(Exception e)
    {
        super(e);
    }
}
