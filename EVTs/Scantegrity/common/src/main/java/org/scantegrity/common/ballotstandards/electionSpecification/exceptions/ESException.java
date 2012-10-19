// Reversed by Rick using JAD decompiler with some tweaks
// Jad home page: http://www.geocities.com/kpdus/jad.html
// Decompiler options: packimports(3) 
// Source File Name:   ESException.java

package org.scantegrity.common.ballotstandards.electionSpecification.exceptions;

import java.io.Serializable;

public class ESException extends Exception
    implements Serializable
{

    /**
	 * 
	 */
	private static final long serialVersionUID = -6275060952032319576L;

	public ESException()
    {
    }

    public ESException(String text)
    {
        super(text);
    }

    public ESException(Exception e)
    {
        super(e);
    }
}
