// Reversed by Rick using JAD decompiler with some tweaks
// Jad home page: http://www.geocities.com/kpdus/jad.html
// Decompiler options: packimports(3) 
// Source File Name:   TallyException.java

package org.scantegrity.common.ballotstandards;

import java.io.Serializable;

public class TallyException extends Exception
    implements Serializable
{

    /**
	 * 
	 */
	private static final long serialVersionUID = 311341467014540510L;

	public TallyException()
    {
    }

    public TallyException(String text)
    {
        super(text);
    }

    public TallyException(Exception e)
    {
        super(e);
    }
}
