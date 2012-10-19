// Reversed by Rick using JAD decompiler with some tweaks
// Jad home page: http://www.geocities.com/kpdus/jad.html
// Decompiler options: packimports(3) 
// Source File Name:   TallyFatalException.java

package org.scantegrity.common.ballotstandards;

import java.io.Serializable;

public class TallyFatalException extends Exception
    implements Serializable
{

    /**
	 * 
	 */
	private static final long serialVersionUID = 6067167007117102532L;

	public TallyFatalException()
    {
    }

    public TallyFatalException(String text)
    {
        super(text);
    }

    public TallyFatalException(Exception e)
    {
        super(e);
    }
}
