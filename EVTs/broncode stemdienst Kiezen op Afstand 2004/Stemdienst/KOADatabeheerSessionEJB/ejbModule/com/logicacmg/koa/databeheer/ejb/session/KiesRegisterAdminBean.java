/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.databeheer.ejb.session.KiesRegisterAdminBean.java
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
  *  0.1		09-04-2003	MRo			First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.databeheer.ejb.session;
import java.io.IOException;
import java.io.InputStream;
import java.math.BigDecimal;
import java.rmi.RemoteException;
import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Date;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.Map;
import java.util.Properties;
import java.util.TreeMap;

import javax.naming.Context;

import org.xml.sax.Attributes;
import org.xml.sax.InputSource;
import org.xml.sax.SAXException;
import org.xml.sax.XMLReader;
import org.xml.sax.helpers.DefaultHandler;
import org.xml.sax.helpers.XMLReaderFactory;

import com.logica.eplatform.error.ErrorMessageFactory;
import com.logica.eplatform.util.XMLProperties;
import com.logicacmg.koa.constants.ComponentType;
import com.logicacmg.koa.constants.ErrorConstants;
import com.logicacmg.koa.constants.FunctionalProps;
import com.logicacmg.koa.constants.JNDIProperties;
import com.logicacmg.koa.constants.SystemState;
import com.logicacmg.koa.constants.TechnicalProps;
import com.logicacmg.koa.databeheer.data.KiezerData;
import com.logicacmg.koa.databeheer.ejb.session.KiesRegisterAdminHelper;
import com.logicacmg.koa.databeheer.ejb.session.KiesRegisterAdminHelperHome;
import com.logicacmg.koa.databeheer.xml.KiesRegisterExportWriter;
import com.logicacmg.koa.databeheer.xml.WrongIdWriter;
import com.logicacmg.koa.dataobjects.Fingerprint;
import com.logicacmg.koa.db.DBUtils;
import com.logicacmg.koa.db.DataBeheerDB;
import com.logicacmg.koa.db.ReportsDB;
import com.logicacmg.koa.db.TransactionCodeDB;
import com.logicacmg.koa.eventhandling.AuditEventListener;
import com.logicacmg.koa.exception.KOADataBeheerException;
import com.logicacmg.koa.exception.KOAException;
import com.logicacmg.koa.io.TempFile;
import com.logicacmg.koa.koaschema.Districten;
import com.logicacmg.koa.koaschema.DistrictenHome;
import com.logicacmg.koa.koaschema.DistrictenKey;
import com.logicacmg.koa.koaschema.KieskringenHome;
import com.logicacmg.koa.koaschema.KieskringenKey;
import com.logicacmg.koa.kr.beans.KRFingerprints;
import com.logicacmg.koa.kr.beans.KRFingerprintsHome;
import com.logicacmg.koa.kr.beans.KRSequenceEJB;
import com.logicacmg.koa.kr.beans.KRSequenceEJBHome;
import com.logicacmg.koa.kr.beans.KRSequenceEJBKey;
import com.logicacmg.koa.kr.beans.KiezersHome;
import com.logicacmg.koa.sar.SarHome;
import com.logicacmg.koa.security.KOAEncryptionUtil;
import com.logicacmg.koa.utils.KOALogHelper;
import com.logicacmg.koa.utils.ObjectCache;
/**
 * Bean implementation class for Enterprise Bean: KiesRegisterAdmin
 * 
 * Class that process the kies register upload or removes it
 * 
 * 
 */
public class KiesRegisterAdminBean implements javax.ejb.SessionBean
{
	private javax.ejb.SessionContext mySessionCtx;
	private static final Map xStateMapping = new TreeMap();
	private final static String KRSEQUENCE_TABLENAME = "KRFINGERPRINTS";
	private final static String AUDIT_MESSAGE_FINGERPRINT_CREATE =
		"Vingerafdruk statische deel van de KR is aangemaakt met waarde: ";
	// this code wil be executed at class loading
	static {
		xStateMapping.put(
			"kieslijst-replace",
			new String[] { SystemState.PREPARE });
		xStateMapping.put(
			"kiezersregister-delete",
			new String[] { SystemState.OPEN, SystemState.PREPARE });
		xStateMapping.put(
			"kiezersregister-append",
			new String[] { SystemState.OPEN, SystemState.PREPARE });
		xStateMapping.put(
			"kiezersregister-replace",
			new String[] { SystemState.PREPARE });
	}
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
	 * remote methode that starts the processing of the import 
	 * it has the following functions
	 * check state
	 * remove kiesregister if it's a replace upload file
	 * parse
	 * store report
	 * export kieslijst
	 * store export
	 * create static fingerprint
	 * store fingerprint
	 * remove upload file
	 * 
	 * @param id id of the row in the importtemp tabel with the upload file
	 */
	public void processImport(int iTempID) throws KOAException
	{
		Connection xConnKoa = null;
		Connection xConnKr = null;
		PreparedStatement xPre = null;
		ErrorMessageFactory msgFactory = null;
		try
		{
			msgFactory = ErrorMessageFactory.getErrorMessageFactory();
		}
		catch (IOException ioe)
		{
			throw new KOAException(
				"[KiesRegisterAdminBean] failed to get ErrorMessageFactory",
				ioe);
		}
		KOALogHelper.audit(
			KOALogHelper.INFO,
			AuditEventListener.DATA_MANAGEMENT,
			"KiesRegisterAdminBean",
			"Systeem",
			msgFactory.getErrorMessage(
				ErrorConstants.IMPORT_KIESREGISTER_START,
				null));
		KOALogHelper.log(
			KOALogHelper.INFO,
			"[KiesRegisterAdminBean] process import");
		// database
		DBUtils xDbKoa =
			new DBUtils(
				JNDIProperties.getProperty(JNDIProperties.DATASOURCE_KOA));
		DBUtils xDbKr =
			new DBUtils(
				JNDIProperties.getProperty(JNDIProperties.DATASOURCE_KR));
		SimpleDateFormat xFormater = new SimpleDateFormat("dd.MM.yyyy HH:mm");
		try
		{
			Date xStartDate = new Date(System.currentTimeMillis());
			// get connection to koa database
			xConnKoa = xDbKoa.getConnection();
			xConnKoa.setAutoCommit(true);
			// get connection to kr database
			xConnKr = xDbKr.getConnection();
			xConnKr.setAutoCommit(true);
			// check if the state is correct
			String sAction = checkState(iTempID, xDbKoa, xConnKoa);
			KOALogHelper.log(
				KOALogHelper.INFO,
				"[KiesRegisterAdminBean] check state OK");
			KOALogHelper.log(
				KOALogHelper.INFO,
				"[KiesRegisterAdminBean] sAction = " + sAction);
			if (sAction.equals("replace"))
			{
				KOALogHelper.log(
					KOALogHelper.INFO,
					"[KiesRegisterAdminBean] start to empty the kiezers table");
				// empty the kiezers table
				removeKiezers(xDbKr, xConnKr);
				TransactionCodeDB.removeTransactionCodes();
				KOALogHelper.log(
					KOALogHelper.INFO,
					"[KiesRegisterAdminBean] remove kiesregister OK");
			}
			KOALogHelper.log(
				KOALogHelper.INFO,
				"[KiesRegisterAdminBean] start parsing");
			// parse xml and commit data in the database
			XMLProperties xProp = parser(iTempID, xDbKoa, xConnKoa);
			KOALogHelper.log(
				KOALogHelper.INFO,
				"[KiesRegisterAdminBean] parse OK");
			// create temp file
			TempFile xTemp =
				new TempFile(
					TechnicalProps.getProperty(TechnicalProps.TEMPDIR_REPORT));
			// export kieslijst
			int iNumberOfRecords =
				exportKiesRegister(
					xProp,
					xTemp,
					xDbKoa,
					xConnKoa,
					xConnKr,
					sAction);
			xProp.put(
				"data_numberofrecords",
				new Integer(iNumberOfRecords).toString());
			KOALogHelper.log(
				KOALogHelper.INFO,
				"[KiesRegisterAdminBean] export kiesregister OK");
			// store export in database
			ReportsDB.storeReport(
				xTemp,
				FunctionalProps.EXPORT_KIEZERSREGISTER,
				xDbKoa,
				xConnKoa);
			KOALogHelper.log(
				KOALogHelper.INFO,
				"[KiesRegisterAdminBean] store export OK");
			// create static fingerprint
			Fingerprint xFingerprint = createStaticFingerprint();
			KOALogHelper.log(
				KOALogHelper.INFO,
				"[KiesRegisterAdminBean] create static fingerprint OK");
			// store fingerprint			
			saveFingerprint(
				xFingerprint,
				getCurrentState(),
				Fingerprint.KR_STATIC_FINGERPRINT);
			KOALogHelper.log(
				KOALogHelper.INFO,
				"[KiesRegisterAdminBean] store static fingerprint OK");
			// delete temp file
			xTemp.delete();
			// remove tempdata
			removeImport(iTempID);
			KOALogHelper.log(
				KOALogHelper.INFO,
				"[KiesRegisterAdminBean] remove upload file OK");
			// store the xml report
			Date xEndDate = new Date(System.currentTimeMillis());
			xProp.put("data_time_start", xFormater.format(xStartDate));
			xProp.put("data_time_end", xFormater.format(xEndDate));
			String sReportType = "UNKNOWN";
			if (sAction.equals("replace"))
			{
				sReportType = FunctionalProps.VW_REPLACE_KIEZERS;
			}
			else if (sAction.equals("append"))
			{
				sReportType = FunctionalProps.VW_ADD_KIEZERS;
			}
			else if (sAction.equals("delete"))
			{
				sReportType = FunctionalProps.VW_REMOVE_KIEZERS;
			}
			ReportsDB.storeReport(xProp, sReportType, xDbKoa, xConnKoa);
			if ("delete".equals(sAction))
			{
				String[] params =
					{
						(String) xProp.get("data_import_action"),
						(String) xProp.get("data_metadata_requestreference"),
						(String) xProp.get("data_insert_kiezer"),
						(String) xProp.get("data_notinsert_kiezer")};
				KOALogHelper.audit(
					KOALogHelper.INFO,
					AuditEventListener.DATA_MANAGEMENT,
					"KiesRegisterAdminBean",
					"Systeem",
					msgFactory.getErrorMessage(
						ErrorConstants.DELETE_KIESREGISTER_SUCCESS,
						params));
			}
			else
			{
				String[] params =
					{
						(String) xProp.get("data_import_action"),
						(String) xProp.get("data_metadata_requestreference"),
						(String) xProp.get("data_insert_kiezer"),
						(String) xProp.get("data_notinsert_kiezer"),
						(String) xProp.get("data_notfound_kieskring"),
						(String) xProp.get("data_notfound_district"),
						(String) xProp.get("data_numberofrecords")};
				KOALogHelper.audit(
					KOALogHelper.INFO,
					AuditEventListener.DATA_MANAGEMENT,
					"KiesRegisterAdminBean",
					"Systeem",
					msgFactory.getErrorMessage(
						ErrorConstants.IMPORT_KIESREGISTER_SUCCESS,
						params));
			}
			KOALogHelper.log(
				KOALogHelper.INFO,
				"[KiesRegisterAdminBean] store report OK");
		}
		catch (SQLException qsle)
		{
			String[] params = { String.valueOf(iTempID)};
			KOALogHelper.audit(
				KOALogHelper.INFO,
				AuditEventListener.DATA_MANAGEMENT,
				"KiesRegisterAdminBean",
				"Systeem",
				msgFactory.getErrorMessage(
					ErrorConstants.IMPORT_KIESREGISTER_FAILURE,
					params));
			params = new String[] { "Process import" };
			KOALogHelper.logErrorCode(
				"KiesRegisterAdminBean",
				ErrorConstants.ERR_SQL,
				params,
				qsle);
			throw new KOADataBeheerException(
				KOADataBeheerException.SQL_EXCETION,
				qsle);
		}
		finally
		{
			xDbKoa.closePreparedStatement(xPre);
			xDbKoa.closeConnection(xConnKoa);
			xDbKoa.closeConnection(xConnKr);
		}
	}
	/** 
	 * remote methode that removes a row from the importtemp table
	 * 
	 * @param id id of the row in the importtemp tabel with the upload info
	 */
	public void removeImport(int iTempID) throws KOAException
	{
		Connection xConn = null;
		PreparedStatement xPre = null;
		KOALogHelper.audit(
			KOALogHelper.INFO,
			AuditEventListener.DATA_MANAGEMENT,
			"KiesRegisterAdminBean",
			"Systeem",
			"Start verwijderen import van de kiezers.");
		KOALogHelper.log(
			KOALogHelper.INFO,
			"[KiesRegisterAdminBean] remove import");
		// database
		DBUtils xDB =
			new DBUtils(
				JNDIProperties.getProperty(JNDIProperties.DATASOURCE_KOA));
		try
		{
			// get connection
			xConn = xDB.getConnection();
			xConn.setAutoCommit(true);
			// remove upload from database
			xPre = xConn.prepareStatement(DataBeheerDB.DELETE_TEMP_DATA);
			xPre.setInt(1, iTempID);
			xPre.executeUpdate();
		}
		catch (SQLException qsle)
		{
			String[] params = { "Remove import" };
			KOALogHelper.logErrorCode(
				"KiesRegisterAdminBean",
				ErrorConstants.ERR_SQL,
				params,
				qsle);
			throw new KOADataBeheerException(
				KOADataBeheerException.REMOVE_UPLOAD,
				qsle);
		}
		finally
		{
			xDB.closePreparedStatement(xPre);
			xDB.closeConnection(xConn);
		}
	}
	/**
	 * removes the kiesregister entrys from the database
	 * it removes the al the entrys from the kiezer table
	 * 
	 * @param xDB class that suports non-entity database actions
	 * @param xConn jdbc connection to the database
	 */
	private void removeKiezers(DBUtils xDB, Connection xConn)
		throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[KiesRegisterAdminBean] Entered removeKiezers");
		try
		{
			boolean bContend = true;
			String sFirst = null;
			String sLast = null;
			int iKiezerDelete =
				TechnicalProps.getIntProperty(TechnicalProps.KIEZER_DELETE);
			String sQuery =
				"SELECT stemcode FROM KOA01.KIEZERS ORDER BY stemcode FETCH FIRST "
					+ iKiezerDelete
					+ " ROWS ONLY";
			ResultSet xRsFetch = null;
			PreparedStatement xPreFetch = null;
			PreparedStatement xPreDelete = null;
			while (bContend)
			{
				try
				{
					// select some rows
					xPreFetch =
						xConn.prepareStatement(
							sQuery,
							ResultSet.TYPE_FORWARD_ONLY,
							ResultSet.CONCUR_READ_ONLY);
					KOALogHelper.log(
						KOALogHelper.TRACE,
						"[KiesRegisterAdminBean] Executing SQL");
					xRsFetch = xPreFetch.executeQuery();
					if (xRsFetch.next())
					{
						// get the first
						sFirst = xRsFetch.getString(1);
						sLast = xRsFetch.getString(1);
						// get the last						
						while (xRsFetch.next())
						{
							sLast = xRsFetch.getString(1);
						}
						// delete all rows from first to last
						KOALogHelper.log(
							KOALogHelper.TRACE,
							"[KiesRegisterAdminBean] Start deleting");
						xPreDelete =
							xConn.prepareStatement(DataBeheerDB.DELETE_KIEZERS);
						xPreDelete.setString(1, sFirst);
						xPreDelete.setString(2, sLast);
						KOALogHelper.log(
							KOALogHelper.TRACE,
							"[KiesRegisterAdminBean] Executing delete statement");
						xPreDelete.executeUpdate();
					}
					else
					{
						// now more rows 
						// stop deleting
						KOALogHelper.log(
							KOALogHelper.TRACE,
							"[KiesRegisterAdminBean] No more rows");
						bContend = false;
					}
				}
				finally
				{
					xDB.closeResultSet(xRsFetch);
					xDB.closePreparedStatement(xPreFetch);
					xDB.closePreparedStatement(xPreDelete);
				}
			}
		}
		catch (SQLException sqle)
		{
			String[] params = { "Remove kiezers" };
			KOALogHelper.logErrorCode(
				"KiesRegisterAdminBean",
				ErrorConstants.ERR_SQL,
				params,
				sqle);
			throw new KOADataBeheerException(
				KOADataBeheerException.SQL_EXCETION,
				sqle);
		}
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[KiesRegisterAdminBean] Leaving removeKiezers");
	}
	/**
	 * pars the upload file and stores the data in the database
	 * it also stores the foute id's list
	 * 
	 * @param iTempID id of the row in the importtemp tabel with the upload file
	 * @param xDB class that suports non-entity database actions
	 * @param xConn jdbc connection to the database
	 */
	private XMLProperties parser(int iTempID, DBUtils xDB, Connection xConn)
		throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.INFO,
			"[KiesRegisterAdminBean] Entered parser");
		PreparedStatement xPre = null;
		ResultSet xResult = null;
		try
		{
			TempFile xTemp = null;
			XMLProperties xReport = null;
			try
			{
				// get upload
				xPre =
					xConn.prepareStatement(
						DataBeheerDB.SELECT_UPLOAD_TEMP_DATA,
						ResultSet.TYPE_FORWARD_ONLY,
						ResultSet.CONCUR_READ_ONLY);
				xPre.setInt(1, iTempID);
				xResult = xPre.executeQuery();
				xResult.next();
				InputStream xIn = xResult.getBinaryStream(1);
				String sAction = xResult.getString(2);
				String sType = xResult.getString(3);
				XMLReader xXMLReader =
					XMLReaderFactory.createXMLReader(
						"org.apache.xerces.parsers.SAXParser");
				InputSource xInSource = new InputSource(xIn);
				KOALogHelper.log(
					KOALogHelper.INFO,
					"[KiesRegisterAdminBean] Creating tempfile");
				// create temp file
				xTemp =
					new TempFile(
						TechnicalProps.getProperty(
							TechnicalProps.TEMPDIR_REPORT));
				if (sAction.equals("delete"))
				{
					KOALogHelper.log(
						KOALogHelper.INFO,
						"[KiesRegisterAdminBean] Removing");
					// remove
					RemoveParser xParser = new RemoveParser(xTemp);
					xXMLReader.setContentHandler(xParser);
					xXMLReader.parse(xInSource);
					xReport = xParser.getMetaData();
				}
				else
				{
					KOALogHelper.log(
						KOALogHelper.INFO,
						"[KiesRegisterAdminBean] Update insert");
					// update insert
					ReplaceUpdateParser xParser =
						new ReplaceUpdateParser(xTemp, sAction);
					xXMLReader.setContentHandler(xParser);
					xXMLReader.parse(xInSource);
					KOALogHelper.log(
						KOALogHelper.INFO,
						"[KiesRegisterAdminBean] calling getMetaData");
					xReport = xParser.getMetaData();
					KOALogHelper.log(
						KOALogHelper.INFO,
						"[KiesRegisterAdminBean] getMetaData returns");
				}
			}
			finally
			{
				xDB.closeResultSet(xResult);
				xDB.closePreparedStatement(xPre);
			}
			// store export in database
			KOALogHelper.log(
				KOALogHelper.INFO,
				"[KiesRegisterAdminBean] parser() Storing wrongids");
			ReportsDB.storeReport(
				xTemp,
				FunctionalProps.WRONGIDS_KIEZERS,
				xDB,
				xConn);
			// delete temp file
			xTemp.delete();
			KOALogHelper.log(
				KOALogHelper.INFO,
				"[KiesRegisterAdminBean] Returning from parser");
			return xReport;
		}
		catch (SQLException sqle)
		{
			String[] params = { "Storing temp data" };
			KOALogHelper.logErrorCode(
				"KiesRegisterAdminBean",
				ErrorConstants.ERR_SQL,
				params,
				sqle);
			throw new KOADataBeheerException(
				KOADataBeheerException.SQL_EXCETION,
				sqle);
		}
		catch (SAXException saxe)
		{
			// get the wrapped koaException
			throw (KOAException) saxe.getException();
		}
		catch (java.io.IOException ioe)
		{
			String[] params =
				{
					"File system "
						+ TechnicalProps.getProperty(
							TechnicalProps.TEMPDIR_REPORT)};
			KOALogHelper.logErrorCode(
				"KiesRegisterAdminBean",
				ErrorConstants.ERR_IO,
				params,
				ioe);
			throw new KOADataBeheerException(
				KOADataBeheerException.IO_EXCETION,
				ioe);
		}
	}
	/** 
	 * this is a wrapping methode for geting the current state 
	 * 
	 */
	private String getCurrentState() throws KOAException
	{
		Hashtable htProps = new Hashtable();
		htProps.put(
			Context.INITIAL_CONTEXT_FACTORY,
			JNDIProperties.getProperty(
				JNDIProperties.CONTROLLER_CONTEXT_FACTORY));
		htProps.put(
			Context.PROVIDER_URL,
			JNDIProperties.getProperty(JNDIProperties.CONTROLLER_PROVIDER));
		try
		{
			return ObjectCache.getInstance().getState().getCurrent_state();
		}
		catch (RemoteException re)
		{
			String[] params = { "Controller" };
			KOALogHelper.logErrorCode(
				"KiesRegisterAdminBean",
				ErrorConstants.ERR_REMOTE,
				params,
				re);
			throw new KOADataBeheerException(
				KOADataBeheerException.EJBEXCEPTION,
				re);
		}
	}
	/**
	 *  This methode checks the state and trows a exception if the 
	 *  state is not correct
	 * 
	 * @param id id of the row in the importtemp tabel with the upload file
	 * @param xDB class that suports non-entity database actions
	 * @param xConn jdbc connection to the database
	 * @return String withe the action of the database
	 */
	private String checkState(int iTempID, DBUtils xDB, Connection xConn)
		throws KOAException
	{
		String sType = null;
		String sAction = null;
		try
		{
			// get the type and action from the database
			ResultSet xRS = null;
			PreparedStatement xPre = null;
			try
			{
				xPre =
					xConn.prepareStatement(
						DataBeheerDB.SELECT_TYPE_TEMP_DATA,
						ResultSet.TYPE_FORWARD_ONLY,
						ResultSet.CONCUR_READ_ONLY);
				xPre.setInt(1, iTempID);
				xRS = xPre.executeQuery();
				xRS.next();
				sType = xRS.getString(1);
				sAction = xRS.getString(2);
			}
			finally
			{
				xDB.closeResultSet(xRS);
				xDB.closePreparedStatement(xPre);
			}
			String sCurrentState = getCurrentState();
			String[] saState =
				(String[]) xStateMapping.get(sType + "-" + sAction);
			Iterator xKeySet = xStateMapping.keySet().iterator();
			// check the state
			boolean check = false;
			if (saState != null)
			{
				for (int i = 0; i < saState.length; i++)
				{
					if ((saState != null)
						&& (saState[i].equals(sCurrentState)))
					{
						check = true;
					}
				}
			}
			if (!check)
			{
				throw new KOADataBeheerException(
					KOADataBeheerException.WRONG_STATE);
			}
			return sAction;
		}
		catch (SQLException sqle)
		{
			String[] params = { "Check state" };
			KOALogHelper.logErrorCode(
				"KiesRegisterAdminBean",
				ErrorConstants.ERR_SQL,
				params,
				sqle);
			throw new KOADataBeheerException(
				KOADataBeheerException.SQL_EXCETION,
				sqle);
		}
	}
	/**
	 * export the kiesregister to a xml file (Tempfile) 
	 * 
	 * @param xProp propertie list with metdata of the upload file
	 * @param xFile TempFile where to the export data is writen
	 * @param xDB class that suports non-entity database actions
	 * @param xConn jdbc connection to the database
	 * 
	 * @return int - Indicating the number of records; 0 when something failed
	 */
	private int exportKiesRegister(
		XMLProperties xProp,
		TempFile xFile,
		DBUtils xDbKoa,
		Connection xConnKoa,
		Connection xConnKr,
		String action)
		throws KOAException
	{
		String sAction = action;
		int iNumberOfRecords = 0;
		ResultSet xRsKieskringen = null;
		try
		{
			// auto commit has to be false outerwise the 
			// nested selects (resultsets) won't work
			xConnKoa.setAutoCommit(false);
			xConnKr.setAutoCommit(false);
			// select all kieskringen
			KiesRegisterExportWriter xExport =
				new KiesRegisterExportWriter(xFile.getFileWriter(), sAction);
			PreparedStatement xPreDistrict = null;
			ResultSet xRsDistrict = null;
			PreparedStatement xPreKiezer = null;
			ResultSet xRsKiezer = null;
			String sKieskringNr;
			String sDistrictNr;
			xExport.startMetadata();
			xExport.metadataSubTag(
				"requestreference",
				(String) xProp.get("data_metadata_requestreference"));
			xExport.metadataSubTag(
				"responsereference",
				(String) xProp.get("data_metadata_requestreference"));
			xExport.metadataSubTag(
				"creationtime",
				(String) xProp.get("data_metadata_creationtime"));
			xExport.metadataSubTag(
				"kiezercount",
				DataBeheerDB.selectCount(
					DataBeheerDB.SELECT_COUNT_KIEZERS,
					xDbKoa,
					xConnKr));
			xExport.endMetadata();
			xRsKieskringen =
				xDbKoa.executeResultQuery(
					xConnKoa.createStatement(
						ResultSet.TYPE_FORWARD_ONLY,
						ResultSet.CONCUR_READ_ONLY),
					DataBeheerDB.SELECT_ALL_KIESKRINGEN);
			while (xRsKieskringen.next())
			{
				// add kieskring
				sKieskringNr = xRsKieskringen.getString(1);
				xExport.startKiesKring(sKieskringNr);
				try
				{
					// add district
					xPreDistrict =
						xConnKoa.prepareStatement(
							DataBeheerDB.SELECT_DISTRICTEN,
							ResultSet.TYPE_FORWARD_ONLY,
							ResultSet.CONCUR_READ_ONLY);
					xPreDistrict.setString(1, sKieskringNr);
					xRsDistrict = xPreDistrict.executeQuery();
					while (xRsDistrict.next())
					{
						sDistrictNr = xRsDistrict.getString(1);
						xExport.startDistrict(sDistrictNr);
						try
						{
							// add kiezers
							xPreKiezer =
								xConnKr.prepareStatement(
									DataBeheerDB.SELECT_KIEZERS_ID,
									ResultSet.TYPE_FORWARD_ONLY,
									ResultSet.CONCUR_READ_ONLY);
							xPreKiezer.setString(1, sKieskringNr);
							xPreKiezer.setString(2, sDistrictNr);
							xRsKiezer = xPreKiezer.executeQuery();
							while (xRsKiezer.next())
							{
								xExport.kiezer(
									xRsKiezer.getString(1),
									xRsKiezer.getString(2),
									xRsKiezer.getString(3));
								/* Count number of kiezers */
								iNumberOfRecords++;
							}
						}
						finally
						{
							xDbKoa.closeResultSet(xRsKiezer);
							xDbKoa.closePreparedStatement(xPreKiezer);
						}
						xExport.endDistrict();
					}
				}
				finally
				{
					xDbKoa.closePreparedStatement(xPreDistrict);
					xDbKoa.closeResultSet(xRsDistrict);
				}
				xExport.endKiesKring();
			}
			xExport.close();
			xConnKoa.setAutoCommit(true);
			xConnKr.setAutoCommit(true);
		}
		catch (SQLException sqle)
		{
			String[] params = { "Export kiesregister" };
			KOALogHelper.logErrorCode(
				"KiesRegisterAdminBean",
				ErrorConstants.ERR_SQL,
				params,
				sqle);
			throw new KOADataBeheerException(
				KOADataBeheerException.SQL_EXCETION,
				sqle);
		}
		finally
		{
			xDbKoa.closeResultSet(xRsKieskringen);
		}
		return iNumberOfRecords;
	}
	/**
	 *  This method creates a fingerprint over the static part of the KR
	 * 
	 *  @return Fingerprint the fingerprint
	 */
	private Fingerprint createStaticFingerprint()
		throws com.logicacmg.koa.exception.KOAException
	{
		com.logicacmg.koa.dataobjects.Fingerprint xFingerprint =
			new com.logicacmg.koa.dataobjects.Fingerprint();
		xFingerprint.setFingerprint(
			KOAEncryptionUtil.getFingerPrint(
				JNDIProperties.getProperty(JNDIProperties.DATASOURCE_KR),
				TechnicalProps.KR_SCHEMA_NAME,
				TechnicalProps.KR_TABLE_NAME,
				TechnicalProps.KR_STATIC_COLUMNS,
				TechnicalProps.KR_SORT_KEY));
		xFingerprint.setFingerprintType(Fingerprint.KR_STATIC_FINGERPRINT);
		xFingerprint.setTimestamp(
			new java.sql.Timestamp(System.currentTimeMillis()));
		/* Log the creation of the static fingerprint to the auditlog */
		String sFingerprintMessage =
			AUDIT_MESSAGE_FINGERPRINT_CREATE
				+ KOAEncryptionUtil.fingerprintValueToString(
					xFingerprint.getFingerprint());
		KOALogHelper.audit(
			KOALogHelper.TRACE,
			AuditEventListener.DATA_MANAGEMENT,
			ComponentType.KR,
			"Systeem",
			sFingerprintMessage);
		return xFingerprint;
	}
	/**
	 * store the fingerprint in the database
	 * 
	 * @param xFingerprint the fingerprint
	 * @param sState state of the system
	 * @param iType type of fingerprint
	 */
	private void saveFingerprint(
		Fingerprint xFingerprint,
		String sState,
		short iType)
		throws com.logicacmg.koa.exception.KOAException
	{
		KOALogHelper.log(
			KOALogHelper.INFO,
			"[KiesRegisterAdmin] entered saveFingerprint()");
		KRFingerprints xKRFingerprints = null;
		try
		{
			//get new id
			BigDecimal xKey = getNewID();
			if (xKey != null)
			{
				KRFingerprintsHome xKRFingerprintsHome =
					ObjectCache.getInstance().getKRFingerprintsHome();
				xKRFingerprints =
					xKRFingerprintsHome.create(
						xKey,
						new Short(iType),
						xFingerprint.getFingerprint(),
						xFingerprint.getTimestamp(),
						sState);
			}
		}
		catch (javax.ejb.CreateException xCreateException)
		{
			String[] params = { "xKRFingerprints" };
			KOALogHelper.logErrorCode(
				"KiesRegisterAdminBean",
				ErrorConstants.ERR_CREATE,
				params,
				xCreateException);
			throw new KOADataBeheerException(
				KOADataBeheerException.EJBEXCEPTION,
				xCreateException);
		}
		catch (java.rmi.RemoteException xRemoteExc)
		{
			String[] params = { "xKRFingerprints" };
			KOALogHelper.logErrorCode(
				"KiesRegisterAdminBean",
				ErrorConstants.ERR_REMOTE,
				params,
				xRemoteExc);
			throw new KOADataBeheerException(
				KOADataBeheerException.EJBEXCEPTION,
				xRemoteExc);
		}
	}
	/**
	 * gets a new ID for the fingerprint table
	 * 
	 * @return BigDecimal the new ID
	 */
	private BigDecimal getNewID()
		throws com.logicacmg.koa.exception.KOAException
	{
		BigDecimal xNewID = null;
		try
		{
			KRSequenceEJBHome xKRSequenceEJBHome =
				ObjectCache.getInstance().getKRSequenceEJBHome();
			KRSequenceEJB xKRSequenceEJB =
				xKRSequenceEJBHome.findByPrimaryKey(
					new KRSequenceEJBKey(KRSEQUENCE_TABLENAME));
			if (xKRSequenceEJB != null)
			{
				//retrieve the last generated id
				xNewID = xKRSequenceEJB.getNextID();
				if (xNewID != null)
				{
					//create new id
					xNewID = xNewID.add(new BigDecimal(1));
					//store the new id
					xKRSequenceEJB.setNextID(xNewID);
				}
			}
		}
		catch (javax.ejb.FinderException xFinderException)
		{
			String[] params = { "KRSequenceEJB" };
			KOALogHelper.logErrorCode(
				"KiesRegisterAdminBean",
				ErrorConstants.ERR_FINDER,
				params,
				xFinderException);
			throw new KOADataBeheerException(
				KOADataBeheerException.EJBEXCEPTION,
				xFinderException);
		}
		catch (java.rmi.RemoteException xRemoteExc)
		{
			String[] params = { "KRSequenceEJB" };
			KOALogHelper.logErrorCode(
				"KiesRegisterAdminBean",
				ErrorConstants.ERR_REMOTE,
				params,
				xRemoteExc);
			throw new KOADataBeheerException(
				KOADataBeheerException.EJBEXCEPTION,
				xRemoteExc);
		}
		return xNewID;
	}
	/** 
	 * this is a wrapping methode for the KiesRegisterAdminHelperBean
	 * 
	 * @see KiesRegisterAdminHelperBean#removeKiezer(String)
	 */
	private String removeKiezer(String sKiezer) throws KOAException
	{
		try
		{
			KiesRegisterAdminHelperHome xHome =
				ObjectCache.getInstance().getKiesregisterAdminHelperHome();
			KiesRegisterAdminHelper xBean = xHome.create();
			return xBean.removeKiezer(sKiezer);
		}
		catch (CreateException fe)
		{
			String[] params = { "KiesRegisterAdminHelper" };
			KOALogHelper.logErrorCode(
				"KiesRegisterAdminBean",
				ErrorConstants.ERR_CREATE,
				params,
				fe);
			throw new KOADataBeheerException(
				KOADataBeheerException.EJBEXCEPTION,
				fe);
		}
		catch (RemoteException ne)
		{
			String[] params = { "KiesRegisterAdminHelper" };
			KOALogHelper.logErrorCode(
				"KiesRegisterAdminBean",
				ErrorConstants.ERR_REMOTE,
				params,
				ne);
			throw new KOADataBeheerException(
				KOADataBeheerException.EJBEXCEPTION,
				ne);
		}
	}
	/** 
	 * helper methode to create a kiezersHome interface
	 * 
	 * @return KiezersHome kiezers entity
	 */
	private KiezersHome getKiezersHome() throws KOAException
	{
		return ObjectCache.getInstance().getKiezersHome();
	}
	/** 
	 * helper methode to create a SarHome interface
	 * 
	 * @return SarHome sar entity
	 */
	private SarHome getSarHome() throws KOAException
	{
		return ObjectCache.getInstance().getSARHome();
	}
	/** 
	 * helper methode to create a KiesRegisterAdminHelper interface
	 * 
	 * @return KiesRegisterAdminHelper KiesRegisterAdminHelper remote  
	 */
	private KiesRegisterAdminHelper getHelperBeanRemote() throws KOAException
	{
		try
		{
			KiesRegisterAdminHelperHome xHome =
				ObjectCache.getInstance().getKiesregisterAdminHelperHome();
			return xHome.create();
		}
		catch (RemoteException re)
		{
			String[] params = { "KiesRegisterAdminHelperHome" };
			KOALogHelper.logErrorCode(
				"KiesRegisterAdminBean",
				ErrorConstants.ERR_REMOTE,
				params,
				re);
			throw new KOADataBeheerException(
				KOADataBeheerException.EJBEXCEPTION,
				re);
		}
		catch (CreateException ce)
		{
			String[] params = { "KiesRegisterAdminHelperHome" };
			KOALogHelper.logErrorCode(
				"KiesRegisterAdminBean",
				ErrorConstants.ERR_CREATE,
				params,
				ce);
			throw new KOADataBeheerException(
				KOADataBeheerException.EJBEXCEPTION,
				ce);
		}
	}
	/** 
	 * helper methode to create a KieskringenHome interface
	 * 
	 * @return KieskringenHome kieskring entity
	 */
	private KieskringenHome getKieskringenHome() throws KOAException
	{
		return ObjectCache.getInstance().getKieskringenHome();
	}
	/** 
	 * helper methode to create a DistrictenHome interface
	 * 
	 * @return DistrictenHome Districten entity
	 */
	private DistrictenHome getDistrictenHome() throws KOAException
	{
		return ObjectCache.getInstance().getDistrictenHome();
	}
	/**	
	 * This class is the parser implementation for het replace and update upload bestand
	 */
	private class ReplaceUpdateParser extends DefaultHandler
	{
		private String IMPORT = "import";
		private String ACTION = "action";
		private String CONTENT_TYPE = "contenttype";
		private String META_DATA = "metadata";
		private String KIESKRING = "kieskring";
		private String DISTRICT = "district";
		private String KIEZER = "kiezer";
		private String HASHEDWW = "hashedww";
		private String NUMMER = "nummer";
		private String ID = "id";
		private String META_DATA_TAG = "data_metadata_";
		private String COUNT_TAG = "data_count_";
		private String NOT_INSERT_TAG = "data_notinsert_";
		private String INSERT_TAG = "data_insert_";
		private String IMPORT_TAG = "data_import_";
		private String NOTFOUND_TAG = "data_notfound_";
		private KiezerData xKiezer;
		private int iKieskring;
		private int iDistrict;
		private int iKiezer;
		private int iKiezersInsert;
		private int iKiezersNotInsert;
		private int iKieskringNotFound;
		private int iDistrictNotFound;
		private int iKiezerCommit;
		private boolean bMetaData;
		private boolean bHasedWW;
		private String sAction;
		private ArrayList xKiezersList = new ArrayList();
		private XMLProperties xMetaProps = new XMLProperties(new Properties());
		private String sTmpQName;
		private TempFile xTempFile;
		private WrongIdWriter xWriter;
		// refference to the home interface
		private KiesRegisterAdminHelper xHelperBeanRemote;
		private DistrictenHome xDistrictenHome;
		private KieskringenHome xKieskringenHome;
		private KiezersHome xKiezersHome;
		private SarHome xSarHome;
		/**
		 * constructor
		 * 
		 * @param xTempFile the file where to the foute id's xml is written to
		 * @param sAction wiche type of upload 
		 */
		public ReplaceUpdateParser(TempFile xTempFile, String sAction)
		{
			this.xTempFile = xTempFile;
			this.sAction = sAction;
			this.xKiezer = new KiezerData();
		}
		/**
		 * creates a foute id's writer
		 * @see DefaultHandler#startDocument()
		 */
		public void startDocument() throws SAXException
		{
			try
			{
				xWriter = new WrongIdWriter(xTempFile.getFileWriter());
				iKiezerCommit =
					TechnicalProps.getIntProperty(TechnicalProps.KIEZER_COMMIT);
				xHelperBeanRemote = getHelperBeanRemote();
				xDistrictenHome = getDistrictenHome();
				xKieskringenHome = getKieskringenHome();
				xKiezersHome = getKiezersHome();
				xSarHome = getSarHome();
			}
			catch (KOAException koae)
			{
				// wrap exception
				throw new SAXException(koae);
			}
		}
		/**
		 * processe al the element and stores them in the database
		 * @see DefaultHandler#startElement(String sUri, String sLocalname, String sQName, Attributes xAttributes)
		 */
		public void startElement(
			String sUri,
			String sLocalname,
			String sQName,
			Attributes xAttributes)
			throws SAXException
		{
			try
			{
				if (bMetaData)
				{
					// store the tag name in the sTmpQName for adding to the xMetaProps
					sTmpQName = sQName;
				}
				// HASHEDWW tag
				else if (sQName.equals(HASHEDWW))
				{
					bHasedWW = true;
				}
				// KIEZER tag
				else if (sQName.equals(KIEZER))
				{
					//if the kieskring and district excists
					iKiezer++;
					xKiezer.setKiezer(xAttributes.getValue(ID));
				}
				// district tag
				else if (sQName.equals(DISTRICT))
				{
					iDistrict++;
					//if the kies kring excists
					xKiezer.setDistrict(xAttributes.getValue(NUMMER));
					if (!xKiezer.getErrorKieskring())
					{
						try
						{
							// find the distict
							Districten xDistricten =
								xDistrictenHome.findByPrimaryKey(
									new DistrictenKey(xKiezer.getDistrict()));
							if (!xDistricten
								.getFk_dist_kkrKey()
								.kieskringnummer
								.equals(xKiezer.getKieskring()))
							{
								// District does not exist for the kieskring
								iDistrictNotFound++;
								xKiezer.setErrorDistrict();
							}
						}
						catch (FinderException ce)
						{
							iDistrictNotFound++;
							xWriter.writeDistrict(
								xKiezer.getDistrict(),
								xKiezer.getKieskring(),
								xWriter.NOT_FOUND);
							xKiezer.setErrorDistrict();
						}
					}
					else
					{
						iDistrictNotFound++;
						xWriter.writeDistrict(
							xKiezer.getDistrict(),
							xKiezer.getKieskring(),
							xWriter.NOT_FOUND_KIESKRING);
					}
				}
				// kieskring tag
				else if (sQName.equals(KIESKRING))
				{
					xKiezer.setKieskring(xAttributes.getValue(NUMMER));
					try
					{
						// find the kiezer
						xKieskringenHome.findByPrimaryKey(
							new KieskringenKey(xKiezer.getKieskring()));
					}
					catch (FinderException ce)
					{
						iKieskringNotFound++;
						xWriter.writeKiesKring(
							xKiezer.getKieskring(),
							xWriter.NOT_FOUND);
						// set an kieskring error 
						xKiezer.setErrorKieskring();
					}
					iKieskring++;
				}
				// metadata tag
				else if (sQName.equals(META_DATA))
				{
					bMetaData = true;
				}
				// check the "import" tag.
				else if (sQName.equals(IMPORT))
				{
					String sAction = xAttributes.getValue(ACTION);
					String sContentType = xAttributes.getValue(CONTENT_TYPE);
					xMetaProps.put(IMPORT_TAG + ACTION, sAction);
					xMetaProps.put(IMPORT_TAG + CONTENT_TYPE, sContentType);
				}
			}
			catch (KOAException koae)
			{
				// wrap exception				
				throw new SAXException(koae);
			}
			catch (RemoteException re)
			{
				// wrap exception		
				String[] params = { "Districten and Kieskringen" };
				KOALogHelper.logErrorCode(
					"KiesRegisterAdminBean",
					ErrorConstants.ERR_REMOTE,
					params,
					re);
				throw new SAXException(
					new KOADataBeheerException(
						KOADataBeheerException.EJBEXCEPTION,
						re));
			}
		}
		/**
		 * Put the tags in the metadata tag in the report properties
		 * @see DefaultHandler#characters(char[], int, int)
		 */
		public void characters(char[] xCharArr, int iStart, int iLength)
			throws SAXException
		{
			try
			{
				if (bMetaData)
				{
					// add tag and CDATA to the xMetaProps
					String sStr = new String(xCharArr, iStart, iLength).trim();
					if (sStr.length() > 0)
					{
						xMetaProps.put(
							META_DATA_TAG + sTmpQName,
							new String(xCharArr, iStart, iLength));
					}
				}
				if (bHasedWW)
				{
					String sStr = new String(xCharArr, iStart, iLength).trim();
					if (sStr.length() > 0)
					{
						//if the kieskring and district exist
						if ((!xKiezer.getErrorKieskring())
							&& (!xKiezer.getErrorDistrict()))
						{
							xKiezer.setHashedWW(sStr);
							// add kiezer to the list
							xKiezersList.add(xKiezer);
						}
						else
						{
							xWriter.writeKiezer(
								xKiezer.getKiezer(),
								xWriter.NOT_FOUND_KIESKRING);
							iKiezersNotInsert++;
						}
						// create new reference and copy needed information
						KiezerData xKiezerTemp = new KiezerData();
						xKiezerTemp.setKieskring(xKiezer.getKieskring());
						xKiezerTemp.setDistrict(xKiezer.getDistrict());
						if (xKiezer.getErrorDistrict())
						{
							xKiezerTemp.setErrorDistrict();
						}
						if (xKiezer.getErrorKieskring())
						{
							xKiezerTemp.setErrorKieskring();
						}
						xKiezer = xKiezerTemp;
						// if commit limmit is reached insert kiezer in the database
						if (xKiezersList.size() > iKiezerCommit)
						{
							String[] saErrorIds;
							KiezerData[] xKiezerData =
								(KiezerData[]) xKiezersList.toArray(
									new KiezerData[xKiezersList.size()]);
							if (sAction.equals("replace"))
							{
								saErrorIds =
									xHelperBeanRemote.insertKiezers(
										xKiezerData,
										xKiezersHome,
										xSarHome);
							}
							else
							{
								saErrorIds =
									xHelperBeanRemote.updateKiezers(
										xKiezerData,
										xKiezersHome,
										xSarHome);
							}
							iKiezersInsert =
								iKiezersInsert
									+ xKiezersList.size()
									- saErrorIds.length;
							iKiezersNotInsert =
								iKiezersNotInsert + saErrorIds.length;
							for (int i = 0; i < saErrorIds.length; i++)
							{
								xWriter.writeKiezer(
									saErrorIds[i],
									"notInserted");
							}
							xKiezersList = new ArrayList();
						}
					}
				}
			}
			catch (KOAException koae)
			{
				// wrap exception				
				throw new SAXException(koae);
			}
			catch (RemoteException re)
			{
				// wrap exception		
				String[] params = { "Kiezer" };
				KOALogHelper.logErrorCode(
					"KiesRegisterAdminBean",
					ErrorConstants.ERR_REMOTE,
					params,
					re);
				throw new SAXException(
					new KOADataBeheerException(
						KOADataBeheerException.EJBEXCEPTION,
						re));
			}
		}
		/**
		 * if metadata has ended
		 * @see DefaultHandler#endElement(String, String, String)
		 */
		public void endElement(String sUri, String sLocalname, String sQName)
			throws SAXException
		{
			if (sQName.equals(META_DATA))
			{
				// end the adding to the xMetaProps
				bMetaData = false;
			}
			if (sQName.equals(HASHEDWW))
			{
				// end tag HASHEDWW
				bHasedWW = false;
			}
		}
		/**
		 * put all the counted tag in the report properties
		 * @see DefaultHandler#endDocument()
		 */
		public void endDocument() throws SAXException
		{
			try
			{
				if (xKiezersList.size() > 0)
				{
					// process the kiesers that are left
					String[] saErrorIds;
					KiezerData[] xKiezerData =
						(KiezerData[]) xKiezersList.toArray(
							new KiezerData[xKiezersList.size()]);
					if (sAction.equals("replace"))
					{
						saErrorIds =
							xHelperBeanRemote.insertKiezers(
								xKiezerData,
								xKiezersHome,
								xSarHome);
					}
					else
					{
						saErrorIds =
							xHelperBeanRemote.updateKiezers(
								xKiezerData,
								xKiezersHome,
								xSarHome);
					}
					iKiezersInsert =
						iKiezersInsert
							+ xKiezersList.size()
							- saErrorIds.length;
					iKiezersNotInsert = iKiezersNotInsert + saErrorIds.length;
					for (int i = 0; i < saErrorIds.length; i++)
					{
						xWriter.writeKiezer(saErrorIds[i], "notInserted");
					}
				}
				xMetaProps.put(
					COUNT_TAG + KIESKRING,
					(new Integer(iKieskring)).toString());
				xMetaProps.put(
					COUNT_TAG + DISTRICT,
					(new Integer(iDistrict)).toString());
				xMetaProps.put(
					COUNT_TAG + KIEZER,
					(new Integer(iKiezer)).toString());
				xMetaProps.put(
					NOTFOUND_TAG + KIESKRING,
					(new Integer(iKieskringNotFound)).toString());
				xMetaProps.put(
					NOTFOUND_TAG + DISTRICT,
					(new Integer(iDistrictNotFound)).toString());
				xMetaProps.put(
					INSERT_TAG + KIEZER,
					(new Integer(iKiezersInsert)).toString());
				xMetaProps.put(
					NOT_INSERT_TAG + KIEZER,
					Integer.toString(iKiezersNotInsert));
				xWriter.close();
			}
			catch (KOAException koae)
			{
				// wrap exception				
				throw new SAXException(koae);
			}
			catch (RemoteException re)
			{
				// wrap exception		
				String[] params = { "KiesRegisterHelperBean" };
				KOALogHelper.logErrorCode(
					"KiesRegisterAdminBean",
					ErrorConstants.ERR_REMOTE,
					params,
					re);
				throw new SAXException(
					new KOADataBeheerException(
						KOADataBeheerException.EJBEXCEPTION,
						re));
			}
		}
		/**
		 * returns the report properties
		 * @return XMLProperties report properties
		 */
		public XMLProperties getMetaData()
		{
			return xMetaProps;
		}
	}
	/**	
	 * This class is the parser implementation for het replace and update upload bestand
	 */
	private class RemoveParser extends DefaultHandler
	{
		private String IMPORT = "import";
		private String ACTION = "action";
		private String CONTENT_TYPE = "contenttype";
		private String META_DATA = "metadata";
		private String KIEZER = "kiezer";
		private String ID = "id";
		private String META_DATA_TAG = "data_metadata_";
		private String COUNT_TAG = "data_count_";
		private String IMPORT_TAG = "data_import_";
		private String REMOVED_TAG = "data_insert_";
		private String NOTFOUND_TAG = "data_notinsert_";
		private int iRemovedKiezers;
		private int iKiezer;
		private int iNotFoundKiezers;
		private boolean bMetaData;
		private XMLProperties xMetaProps = new XMLProperties(new Properties());
		private String sTmpQName;
		private TempFile xTempFile;
		private WrongIdWriter xWriter;
		/**
		 * constructor
		 * 
		 * @param xTempFile the file where to the foute id's xml is written to
		 */
		public RemoveParser(TempFile xTempFile)
		{
			this.xTempFile = xTempFile;
		}
		/**
		 * creates a foute id's writer
		 * @see DefaultHandler#startDocument()
		 */
		public void startDocument() throws SAXException
		{
			try
			{
				xWriter = new WrongIdWriter(xTempFile.getFileWriter());
			}
			catch (KOAException koae)
			{
				// wrap exception				
				throw new SAXException(koae);
			}
		}
		/**
		 * processe al the element and stores them in the database
		 * @see DefaultHandler#startElement(String sUri, String sLocalname, String sQName, Attributes xAttributes)
		 */
		public void startElement(
			String sUri,
			String sLocalname,
			String sQName,
			Attributes xAttributes)
			throws SAXException
		{
			try
			{
				if (bMetaData)
				{
					// store the tag name in the sTmpQName for adding to the xMetaProps
					sTmpQName = sQName;
				}
				// KIEZER tag
				else if (sQName.equals(KIEZER))
				{
					iKiezer++;
					//if the kieskring and district exist
					String sKiezerId = xAttributes.getValue(ID);
					String remove = removeKiezer(xAttributes.getValue(ID));
					if (remove != null)
					{
						iNotFoundKiezers++;
						xWriter.writeKiezer(sKiezerId, remove);
					}
					else
					{
						iRemovedKiezers++;
					}
				}
				// metadata tag
				else if (sQName.equals(META_DATA))
				{
					bMetaData = true;
				}
				// check the "import" tag.
				else if (sQName.equals(IMPORT))
				{
					String sAction = xAttributes.getValue(ACTION);
					String sContentType = xAttributes.getValue(CONTENT_TYPE);
					xMetaProps.put(IMPORT_TAG + ACTION, sAction);
					xMetaProps.put(IMPORT_TAG + CONTENT_TYPE, sContentType);
				}
			}
			catch (KOAException koae)
			{
				// wrap exception				
				throw new SAXException(koae);
			}
		}
		/**
		 * Put the tags in the metadata tag in the report properties
		 * @see DefaultHandler#characters(char[], int, int)
		 */
		public void characters(char[] xCharArr, int iStart, int iLength)
			throws SAXException
		{
			if (bMetaData)
			{
				// add tag and CDATA to the xMetaProps
				String sStr = new String(xCharArr, iStart, iLength).trim();
				if (sStr.length() > 0)
				{
					xMetaProps.put(
						META_DATA_TAG + sTmpQName,
						new String(xCharArr, iStart, iLength));
				}
			}
		}
		/**
		 * if metadata has ended
		 * @see DefaultHandler#endElement(String, String, String)
		 */
		public void endElement(String sUri, String sLocalname, String sQName)
			throws SAXException
		{
			if (sQName.equals(META_DATA))
			{
				// end the adding to the xMetaProps
				bMetaData = false;
			}
		}
		/**
		 * put all the counted tag in the report properties
		 * @see DefaultHandler#endDocument()
		 */
		public void endDocument() throws SAXException
		{
			try
			{
				xMetaProps.put(
					COUNT_TAG + KIEZER,
					(new Integer(iKiezer)).toString());
				xMetaProps.put(
					REMOVED_TAG + KIEZER,
					(new Integer(iRemovedKiezers)).toString());
				xMetaProps.put(
					NOTFOUND_TAG + KIEZER,
					String.valueOf(iNotFoundKiezers));
				xWriter.close();
			}
			catch (KOAException koae)
			{
				// wrap exception				
				throw new SAXException(koae);
			}
		}
		/**
		 * returns the report properties
		 * @return XMLProperties report properties
		 */
		public XMLProperties getMetaData()
		{
			// wrap exception			
			return xMetaProps;
		}
	}
}