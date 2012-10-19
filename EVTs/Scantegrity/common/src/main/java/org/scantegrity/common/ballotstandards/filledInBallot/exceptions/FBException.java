// Reversed by Rick using JAD decompiler with some tweaks
// Jad home page: http://www.geocities.com/kpdus/jad.html
// Decompiler options: packimports(3) 
// Source File Name:   FBException.java

package org.scantegrity.common.ballotstandards.filledInBallot.exceptions;

import java.io.Serializable;

public class FBException extends Exception
    implements Serializable
{

    /**
	 * 
	 */
	private static final long serialVersionUID = 2353700628193120442L;

	public FBException()
    {
    }

    public FBException(String text)
    {
        super(text);
    }

    public FBException(Exception e)
    {
        super(e);
    }
}
