/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.esb.beans.ESBSessionEJBBean
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
  *  0.1		21-07-2003	XUi	        First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.esb.beans;
import java.sql.Connection;
import java.sql.SQLException;
import java.util.Enumeration;
import java.util.Vector;

import com.logicacmg.koa.constants.ErrorConstants;
import com.logicacmg.koa.constants.JNDIProperties;
import com.logicacmg.koa.constants.TechnicalProps;
import com.logicacmg.koa.dataobjects.DecryptedStem;
import com.logicacmg.koa.db.DBUtils;
import com.logicacmg.koa.exception.KOAException;
import com.logicacmg.koa.utils.KOALogHelper;
/**
 * Bean implementation class for Enterprise Bean: ESBDecryptHelper
 */
public class ESBDecryptHelperBean implements javax.ejb.SessionBean
{
	private javax.ejb.SessionContext mySessionCtx;
	/**
	 * getSessionContext
	 */
	public javax.ejb.SessionContext getSessionContext()
	{
		return mySessionCtx;
	}
	/**
	 * setSessionContext
	 */
	public void setSessionContext(javax.ejb.SessionContext ctx)
	{
		mySessionCtx = ctx;
	}
	/**
	 * ejbActivate
	 */
	public void ejbActivate()
	{
	}
	/**
	 * ejbCreate
	 */
	public void ejbCreate() throws javax.ejb.CreateException
	{
	}
	/**
	 * ejbPassivate
	 */
	public void ejbPassivate()
	{
	}
	/**
	 * ejbRemove
	 */
	public void ejbRemove()
	{
	}
	/**
	 * saveDecryptedVotes 
	 * Impl for better performance.
	 * 
	 * @param Vector decryptedVotes 	A vector with decryptedvotes to store
	 * @param int stemnummerCount		Total amount of decryptedvotes inserted
	 * 
	 * @return int vCount				Total amount of decryptedvotes stored
	 */
	public int saveDecryptedVotes(Vector decryptedVotes, int stemnummerCount)
		throws KOAException, EJBException
	{
		long startTotal = 0;
		if (TechnicalProps.isDebugMode())
		{
			startTotal = System.currentTimeMillis();
		}
		int vCount = stemnummerCount;
		// Store the votes from the vector into the database
		Enumeration enum = decryptedVotes.elements();
		DecryptedStem dVote = null;
		StringBuffer sbQuery = null;
		Connection conn = null;
		// Create statement
		try
		{
			DBUtils xDecryptDBUtils =
				new DBUtils(
					JNDIProperties.getProperty(
						JNDIProperties.DATASOURCE_ESB_NO_TRANS));
			conn = xDecryptDBUtils.getConnection();
			/* set autocommit off for batch commit */
			String sql =
				"INSERT INTO KOA01.DECRYPTEDESB VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?) ";
			java.sql.PreparedStatement stmt = conn.prepareStatement(sql);
			while (enum.hasMoreElements())
			{
				/* clear the params */
				stmt.clearParameters();
				/* get the vote to save */
				dVote = (DecryptedStem) enum.nextElement();
				vCount++;
				/* set the param */
				stmt.setInt(1, vCount);
				stmt.setString(2, dVote.getKandidaatCode());
				stmt.setString(3, dVote.getKieskringnummer());
				stmt.setString(4, dVote.getDistrictnummer());
				stmt.setString(5, dVote.getKieslijstnummer());
				stmt.setString(6, dVote.getPositienummer());
				stmt.setString(7, dVote.getLijstnaam());
				stmt.setString(8, dVote.getAchternaam());
				stmt.setString(9, dVote.getVoorletters());
				stmt.executeUpdate();
			}
			/* commit the batch */
			conn.close();
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[ESBSessionEJBBean] Committed decrypted votes: " + vCount);
		}
		catch (SQLException sqle)
		{
			String[] params = { "saveDecryptedVotes" };
			KOALogHelper.logErrorCode(
				"ESBSessionEJBBean",
				ErrorConstants.ERR_SQL,
				params,
				sqle);
			throw new KOAException(ErrorConstants.ESB_ERROR);
		}
		finally
		{
			try
			{
				conn.close();
			}
			catch (Exception e)
			{
			}
		}
		if (TechnicalProps.isDebugMode())
		{
			long endTotal = System.currentTimeMillis();
			KOALogHelper.log(
				KOALogHelper.INFO,
				"[ESBDecryptHelper.saveDecryptedVotes] Time to insert total subset ("
					+ stemnummerCount
					+ " rows)  in millis: "
					+ (endTotal - startTotal));
		}
		return vCount;
	}
}
