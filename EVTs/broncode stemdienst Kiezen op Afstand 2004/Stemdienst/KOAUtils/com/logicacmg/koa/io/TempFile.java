/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.io.TempFile.java
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
  *  0.1		15-04-2003	MRo			First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.io;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.io.Reader;
import java.io.Writer;

import com.logicacmg.koa.constants.ErrorConstants;
import com.logicacmg.koa.exception.KOADataBeheerException;
import com.logicacmg.koa.exception.KOAException;
import com.logicacmg.koa.utils.KOALogHelper;
/**
 * Creates a tempory file on the file system
 */
public class TempFile
{
	private File xFile;
	/**
	 * It creates a file on the file system in de <code>xDirectory</code>
	 * It chooses a file that does not exist
	 * This constructor differs from the File constuctor that it creates
	 * the file in the constructor.
	 * 
	 * @param xDirectory the directory
	 * 
	 * @throws KOAException when the file can not be created
	 */
	public TempFile(String xDirectory) throws KOAException
	{
		try
		{
			File xDir = new File(xDirectory);
			int i = 0;
			do
			{
				xFile = new File(xDir, "temp" + i);
				i++;
			}
			while (xFile.exists());
			xFile.createNewFile();
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"System file encoding: " + System.getProperty("file.encoding"));
		}
		catch (IOException ioe)
		{
			String[] params = { "Temporary file" };
			KOALogHelper.logErrorCode(
				"TempFile",
				ErrorConstants.ERR_IO,
				params,
				ioe);
			throw new KOADataBeheerException(
				KOADataBeheerException.IO_EXCETION,
				ioe);
		}
	}
	public TempFile(String file, boolean nieuw) throws KOAException
	{
		xFile = new File(file);
	}
	/**
	 * returns a writer to the file
	 * 
	 * @return Writer writer to the file
	 * 
	 * @throws KOAException when something goes wrong creating the writer
	 */
	public Writer getFileWriter() throws KOAException
	{
		try
		{
			return new OutputStreamWriter(new FileOutputStream(xFile), "UTF-8");
		}
		catch (IOException ioe)
		{
			String[] params = { "Temporary file" };
			KOALogHelper.logErrorCode(
				"TempFile",
				ErrorConstants.ERR_IO,
				params,
				ioe);
			throw new KOADataBeheerException(
				KOADataBeheerException.IO_EXCETION,
				ioe);
		}
	}
	/**
	 * returns a reader to the file
	 * 
	 * @return Reader reader to the file
	 * 
	 * @throws KOAException when something goes wrong creating the reader
	 */
	public Reader getFileReader() throws KOAException
	{
		try
		{
			return new InputStreamReader(new FileInputStream(xFile));
		}
		catch (IOException ioe)
		{
			String[] params = { "Temporary file" };
			KOALogHelper.logErrorCode(
				"TempFile",
				ErrorConstants.ERR_IO,
				params,
				ioe);
			throw new KOADataBeheerException(
				KOADataBeheerException.IO_EXCETION,
				ioe);
		}
	}
	/**
	 * length of the file 
	 * @see File#length()
	 * 
	 * @return Reader reader to the file
	 */
	public long length()
	{
		return xFile.length();
	}
	/**
	 * delete the wrapped file from the file system
	 */
	public void delete()
	{
		xFile.delete();
	}
	/**
	 * Returns the file
	 * 
	 * @return File the file
	 * 
	 */
	public File getFile()
	{
		return xFile;
	}
}