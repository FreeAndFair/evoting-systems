/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.databeheer.ejb.session.KieslijstAdminBean.java
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
  *  1.0		09-04-2003	MRo			First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.databeheer.ejb.session;
import java.io.IOException;
import java.io.InputStream;
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
import java.util.List;
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
import com.logicacmg.koa.constants.ErrorConstants;
import com.logicacmg.koa.constants.FunctionalProps;
import com.logicacmg.koa.constants.JNDIProperties;
import com.logicacmg.koa.constants.SystemState;
import com.logicacmg.koa.constants.TechnicalProps;
import com.logicacmg.koa.databeheer.ejb.session.KieslijstAdminHelper;
import com.logicacmg.koa.databeheer.ejb.session.KieslijstAdminHelperHome;
import com.logicacmg.koa.databeheer.xml.KielijstExportWriter;
import com.logicacmg.koa.databeheer.xml.WrongIdWriter;
import com.logicacmg.koa.db.DBUtils;
import com.logicacmg.koa.db.DataBeheerDB;
import com.logicacmg.koa.db.ReportsDB;
import com.logicacmg.koa.eventhandling.AuditEventListener;
import com.logicacmg.koa.exception.KOADataBeheerException;
import com.logicacmg.koa.exception.KOAException;
import com.logicacmg.koa.io.TempFile;
import com.logicacmg.koa.kieslijst.beans.KiesLijst;
import com.logicacmg.koa.kieslijst.beans.KiesLijstHome;
import com.logicacmg.koa.koaschema.Kieslijsten;
import com.logicacmg.koa.utils.KOALogHelper;
import com.logicacmg.koa.utils.ObjectCache;
/**
 * Bean implementation class for Enterprise Bean: KieslijstAdmin
 * 
 * Class that process the kieslijst upload or removes it
 * 
 * 
 */
public class KieslijstAdminBean implements javax.ejb.SessionBean
{
	private javax.ejb.SessionContext mySessionCtx;
	private static final Map xStateMapping = new TreeMap();
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
	 * remove kieslijst
	 * parse
	 * store report
	 * export kieslijst
	 * store export
	 * remove upload file
	 * 
	 * @param id id of the row in the importtemp tabel with the upload file
	 */
	public void processImport(int iTempID) throws KOAException
	{
		Connection xConn = null;
		PreparedStatement xPre = null;
		ErrorMessageFactory msgFactory = null;
		try
		{
			msgFactory = ErrorMessageFactory.getErrorMessageFactory();
		}
		catch (IOException ioe)
		{
			throw new KOAException(
				"[KieslijstAdminBean] failed to get ErrorMessageFactory",
				ioe);
		}
		KOALogHelper.audit(
			KOALogHelper.INFO,
			AuditEventListener.DATA_MANAGEMENT,
			"KieslijstAdminBean",
			"Systeem",
			msgFactory.getErrorMessage(
				ErrorConstants.IMPORT_KIESLIJST_START,
				null));
		KOALogHelper.log(
			KOALogHelper.INFO,
			"[KieslijstAdminBean] process import");
		// database
		DBUtils xDB =
			new DBUtils(
				JNDIProperties.getProperty(JNDIProperties.DATASOURCE_KOA));
		SimpleDateFormat xFormater = new SimpleDateFormat("dd.MM.yyyy HH:mm");
		try
		{
			Date xStartDate = new Date(System.currentTimeMillis());
			// get connection
			xConn = xDB.getConnection();
			xConn.setAutoCommit(true);
			// check if the state is corrct
			checkState(iTempID, xDB, xConn);
			KOALogHelper.log(
				KOALogHelper.INFO,
				"[KieslijstAdminBean] check state OK");
			// empty all kieslijst tables
			removeKieslijst(xDB, xConn);
			KOALogHelper.log(
				KOALogHelper.INFO,
				"[KieslijstAdminBean] remove kieslijst OK");
			// parse xml and commit data in the database
			XMLProperties xProp = parser(iTempID, xDB, xConn);
			KOALogHelper.log(
				KOALogHelper.INFO,
				"[KieslijstAdminBean] parse OK");
			// create temp file
			TempFile xTemp =
				new TempFile(
					TechnicalProps.getProperty(TechnicalProps.TEMPDIR_REPORT));
			// export kieslijst
			exportKiesLijst(xProp, xTemp, xDB, xConn);
			KOALogHelper.log(
				KOALogHelper.INFO,
				"[KieslijstAdminBean] export kieslijst OK");
			// store export in database
			ReportsDB.storeReport(
				xTemp,
				FunctionalProps.EXPORT_KANDIDATENLIJST,
				xDB,
				xConn);
			KOALogHelper.log(
				KOALogHelper.INFO,
				"[KieslijstAdminBean] store export OK");
			// delete temp file
			xTemp.delete();
			// remove tempdata
			removeImport(iTempID);
			KOALogHelper.log(
				KOALogHelper.INFO,
				"[KieslijstAdminBean] remove upload file OK");
			// store the xml report
			Date xEndDate = new Date(System.currentTimeMillis());
			xProp.put("data_time_start", xFormater.format(xStartDate));
			xProp.put("data_time_end", xFormater.format(xEndDate));
			ReportsDB.storeReport(
				xProp,
				FunctionalProps.VW_REPLACE_KANDIDATENLIJST,
				xDB,
				xConn);
			String[] params =
				{
					(String) xProp.get("data_import_action"),
					(String) xProp.get("data_metadata_requestreference"),
					(String) xProp.get("data_insert_kieslijst"),
					(String) xProp.get("data_insert_positie"),
					(String) xProp.get("data_notinsert_positie"),
					(String) xProp.get("data_notfound_kieskring")};
			KOALogHelper.audit(
				KOALogHelper.INFO,
				AuditEventListener.DATA_MANAGEMENT,
				"KieslijstAdminBean",
				"Systeem",
				msgFactory.getErrorMessage(
					ErrorConstants.IMPORT_KIESLIJST_SUCCESS,
					params));
			KOALogHelper.log(
				KOALogHelper.INFO,
				"[KieslijstAdminBean] store report OK");
			this.createFingerprints();
			KOALogHelper.log(
				KOALogHelper.INFO,
				"[KieslijstAdminBean] create fingerprints OK");
		}
		catch (SQLException qsle)
		{
			String[] params = { String.valueOf(iTempID)};
			KOALogHelper.audit(
				KOALogHelper.INFO,
				AuditEventListener.DATA_MANAGEMENT,
				"KieslijstAdminBean",
				"Systeem",
				msgFactory.getErrorMessage(
					ErrorConstants.IMPORT_KIESLIJST_FAILURE,
					params));
			params = new String[] { "Process import with ID " + iTempID };
			KOALogHelper.logErrorCode(
				"KieslijstAdminBean",
				ErrorConstants.ERR_SQL,
				params,
				qsle);
			throw new KOADataBeheerException(
				KOADataBeheerException.PROCESS_KIESLIJST,
				qsle);
		}
		finally
		{
			xDB.closePreparedStatement(xPre);
			xDB.closeConnection(xConn);
		}
	}
	/** 
	 * this is a wrapping methode for the kieslijsdaminHelperbean
	 * 
	 * @see KieslijstAdminHelper#insertKieslijst(String, String, String)
	 */
	private Kieslijsten insertKieslijst(
		String sKiesKringNr,
		String sKieslijstNr,
		String sLijstnaam)
		throws KOAException
	{
		try
		{
			KieslijstAdminHelperHome xHome =
				ObjectCache.getInstance().getKieslijstAdminHelperHome();
			KieslijstAdminHelper xBean = xHome.create();
			return xBean.insertKieslijst(
				sKiesKringNr,
				sKieslijstNr,
				sLijstnaam);
		}
		catch (CreateException ce)
		{
			String[] params = { "kieslijstAdminHelper" };
			KOALogHelper.logErrorCode(
				"KieslijstAdminBean.insertKieslijst",
				ErrorConstants.ERR_CREATE,
				params,
				ce);
			throw new KOADataBeheerException(
				KOADataBeheerException.CREATE_LIJSTPOS_EXCETION);
		}
		catch (RemoteException ne)
		{
			String[] params = { "kieslijstAdminHelper" };
			KOALogHelper.logErrorCode(
				"KieslijstAdminBean.insertKieslijst",
				ErrorConstants.ERR_REMOTE,
				params,
				ne);
			throw new KOADataBeheerException(
				KOADataBeheerException.EJBEXCEPTION);
		}
	}
	/** 
	 * this is a wrapping methode for the kieslijsdaminHelperbean
	 * 
	 * @see KieslijstAdminHelper#insertLijstPostitie(Kieslijsten, String, String, String, String, char, String)
	 */
	private void insertLijstPostitie(
		Kieslijsten xKieslijst,
		String sPositieNr,
		String sAchternaam,
		String sVoorletters,
		String sRoepnaam,
		char sGeslacht,
		String sWoonplaats)
		throws KOAException
	{
		try
		{
			KieslijstAdminHelperHome xHome =
				ObjectCache.getInstance().getKieslijstAdminHelperHome();
			KieslijstAdminHelper xBean = xHome.create();
			xBean.insertLijstPostitie(
				xKieslijst,
				sPositieNr,
				sAchternaam,
				sVoorletters,
				sRoepnaam,
				sGeslacht,
				sWoonplaats);
		}
		catch (CreateException ce)
		{
			String[] params = { "kieslijstAdminHelper" };
			KOALogHelper.logErrorCode(
				"KieslijstAdminBean",
				ErrorConstants.ERR_CREATE,
				params,
				ce);
			throw new KOADataBeheerException(
				KOADataBeheerException.CREATE_LIJSTPOS_EXCETION);
		}
		catch (RemoteException ne)
		{
			String[] params = { "kieslijstAdminHelper" };
			KOALogHelper.logErrorCode(
				"KieslijstAdminBean",
				ErrorConstants.ERR_REMOTE,
				ne);
			throw new KOADataBeheerException(
				KOADataBeheerException.EJBEXCEPTION);
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
			"KieslijstAdminBean",
			"Systeem",
			"Start verwijderen import van de kandidatenlijsten.");
		KOALogHelper.log(
			KOALogHelper.INFO,
			"[KieslijstAdminBean] remove import");
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
			String[] params = { "remove the import with ID " + iTempID };
			KOALogHelper.logErrorCode(
				"KieslijstAdminBean",
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
	 * removes the kieslijst entrys from the database
	 * it removes the folowing tables
	 * kieslijsten
	 * lijstposities
	 * kandidaatcodes
	 * 
	 * @param xDB class that suports non-entity database actions
	 * @param xConn jdbc connection to the database
	 */
	private void removeKieslijst(DBUtils xDB, Connection xConn)
		throws KOAException
	{
		ResultSet xKieslijstNummers = null;
		try
		{
			// select all kieslijstnummers from kieslijst
			xKieslijstNummers =
				xDB.executeResultQuery(
					xConn.createStatement(
						ResultSet.TYPE_FORWARD_ONLY,
						ResultSet.CONCUR_READ_ONLY),
					DataBeheerDB.SELECT_ALL_KIESLIJSTEN);
			PreparedStatement xPre = null;
			List xList = new ArrayList();
			// cannot delete if an record set is open
			while (xKieslijstNummers.next())
			{
				xList.add(xKieslijstNummers.getString(1));
			}
			String sKieslijstNr;
			Iterator xIter = xList.iterator();
			while (xIter.hasNext())
			{
				sKieslijstNr = (String) xIter.next();
				// remove kandidaatcodes
				try
				{
					xPre =
						xConn.prepareStatement(
							DataBeheerDB.DELETE_KANDIDAATCODES);
					xPre.setString(1, sKieslijstNr);
					xPre.executeUpdate();
					//xConn.commit();
				}
				finally
				{
					xDB.closePreparedStatement(xPre);
				}
				// remove lijstposisties
				try
				{
					xPre =
						xConn.prepareStatement(DataBeheerDB.DELETE_LIJSTPOSIES);
					xPre.setString(1, sKieslijstNr);
					xPre.executeUpdate();
				}
				finally
				{
					xDB.closePreparedStatement(xPre);
				}
			}
			try
			{
				xPre = xConn.prepareStatement(DataBeheerDB.DELETE_KIESLIJSTEN);
				xPre.executeUpdate();
				xConn.commit();
			}
			finally
			{
				xDB.closePreparedStatement(xPre);
			}
		}
		catch (SQLException sqle)
		{
			String[] params = { "Remove Kieslijst" };
			KOALogHelper.logErrorCode(
				"KieslijstAdminBean",
				ErrorConstants.ERR_SQL,
				params,
				sqle);
			throw new KOADataBeheerException(
				KOADataBeheerException.IO_EXCETION,
				sqle);
		}
		finally
		{
			xDB.closeResultSet(xKieslijstNummers);
		}
	}
	/**
	 * pars the upload file and stores the data in the database
	 * it also stores the foute id's list
	 * 
	 * @param id id of the row in the importtemp tabel with the upload file
	 * @param xDB class that suports non-entity database actions
	 * @param xConn jdbc connection to the database
	 */
	private XMLProperties parser(int iTempID, DBUtils xDB, Connection xConn)
		throws KOAException, SQLException
	{
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
				// create temp file
				xTemp =
					new TempFile(
						TechnicalProps.getProperty(
							TechnicalProps.TEMPDIR_REPORT));
				KieslijstParser xParser = new KieslijstParser(xTemp);
				xXMLReader.setContentHandler(xParser);
				xXMLReader.parse(xInSource);
				xReport = xParser.getMetaData();
			}
			finally
			{
				xDB.closeResultSet(xResult);
				xDB.closePreparedStatement(xPre);
			}
			// store export in database
			ReportsDB.storeReport(
				xTemp,
				FunctionalProps.WRONGIDS_KANDIDATENLIJST,
				xDB,
				xConn);
			// delete temp file
			xTemp.delete();
			return xReport;
		}
		catch (SAXException saxe)
		{
			// retrow wraped exception
			throw (KOAException) saxe.getException();
		}
		catch (java.io.IOException ioe)
		{
			String[] params =
				{
					"File system location "
						+ TechnicalProps.getProperty(
							TechnicalProps.TEMPDIR_REPORT)};
			KOALogHelper.logErrorCode(
				"KieslijstAdminBean",
				ErrorConstants.ERR_IO,
				params,
				ioe);
			throw new KOADataBeheerException(
				KOADataBeheerException.PROCESS_KIESLIJST,
				ioe);
		}
	}
	/**
	 * export the kieslijst to a xml file (Tempfile) 
	 * 
	 * @param xProp propertie list with metdata of the upload file
	 * @param xFile TempFile where to the export data is writen
	 * @param xDB class that suports non-entity database actions
	 * @param xConn jdbc connection to the database
	 */
	private void exportKiesLijst(
		XMLProperties xProp,
		TempFile xFile,
		DBUtils xDB,
		Connection xConn)
		throws KOAException
	{
		ResultSet xRsKieskringen = null;
		try
		{
			xConn.setAutoCommit(false);
			KielijstExportWriter xExport =
				new KielijstExportWriter(xFile.getFileWriter());
			PreparedStatement xPreDistrict = null;
			ResultSet xRsDistrict = null;
			PreparedStatement xPreKieslijst = null;
			ResultSet xRsKieslijst = null;
			PreparedStatement xPrePositie = null;
			ResultSet xRsPositie = null;
			PreparedStatement xPreCode = null;
			ResultSet xRsCode = null;
			ResultSet xRsMax = null;
			String sKieskringNr;
			String sKieslijstNr;
			String sPositieNr;
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
			// select count from kieskringen
			xExport.metadataSubTag(
				"kieskringcount",
				DataBeheerDB.selectCount(
					DataBeheerDB.SELECT_COUNT_KIESKRINGEN,
					xDB,
					xConn));
			// select count from districten
			xExport.metadataSubTag(
				"districtcount",
				DataBeheerDB.selectCount(
					DataBeheerDB.SELECT_COUNT_DISTRICTEN,
					xDB,
					xConn));
			// select count from kieslijsten
			xExport.metadataSubTag(
				"kieslijstcount",
				DataBeheerDB.selectCount(
					DataBeheerDB.SELECT_COUNT_KIESLIJSTEN,
					xDB,
					xConn));
			// select count from lijstposities
			xExport.metadataSubTag(
				"positiecount",
				DataBeheerDB.selectCount(
					DataBeheerDB.SELECT_COUNT_LIJSTPOSITIES,
					xDB,
					xConn));
			// select count from code
			xExport.metadataSubTag(
				"codecount",
				DataBeheerDB.selectCount(
					DataBeheerDB.SELECT_COUNT_KANDIDAATCODES,
					xDB,
					xConn));
			xExport.endMetadata();
			xRsKieskringen =
				xDB.executeResultQuery(
					xConn.createStatement(
						ResultSet.TYPE_FORWARD_ONLY,
						ResultSet.CONCUR_READ_ONLY),
					DataBeheerDB.SELECT_ALL_KIESKRINGEN);
			while (xRsKieskringen.next())
			{
				// add kieskring
				sKieskringNr = xRsKieskringen.getString(1);
				xExport.startKiesKring(
					sKieskringNr,
					xRsKieskringen.getString(2));
				try
				{
					// add district
					xPreDistrict =
						xConn.prepareStatement(
							DataBeheerDB.SELECT_DISTRICTEN,
							ResultSet.TYPE_FORWARD_ONLY,
							ResultSet.CONCUR_READ_ONLY);
					xPreDistrict.setString(1, sKieskringNr);
					xRsDistrict = xPreDistrict.executeQuery();
					while (xRsDistrict.next())
					{
						xExport.district(
							xRsDistrict.getString(1),
							xRsDistrict.getString(2));
					}
				}
				finally
				{
					xDB.closePreparedStatement(xPreDistrict);
					xDB.closeResultSet(xRsDistrict);
				}
				try
				{
					// add kieslijst
					xPreKieslijst =
						xConn.prepareStatement(
							DataBeheerDB.SELECT_KIESLIJSTEN,
							ResultSet.TYPE_FORWARD_ONLY,
							ResultSet.CONCUR_READ_ONLY);
					xPreKieslijst.setString(1, sKieskringNr);
					xRsKieslijst = xPreKieslijst.executeQuery();
					while (xRsKieslijst.next())
					{
						sKieslijstNr = xRsKieslijst.getString(1);
						xExport.startKiesLijst(
							sKieslijstNr,
							xRsKieslijst.getString(2));
						try
						{
							// add posities
							xPrePositie =
								xConn.prepareStatement(
									DataBeheerDB.SELECT_LIJSTPOSITIES,
									ResultSet.TYPE_FORWARD_ONLY,
									ResultSet.CONCUR_READ_ONLY);
							xPrePositie.setString(1, sKieskringNr);
							xPrePositie.setString(2, sKieslijstNr);
							xRsPositie = xPrePositie.executeQuery();
							while (xRsPositie.next())
							{
								sPositieNr = xRsPositie.getString(1);
								xExport.startPositie(
									sPositieNr,
									xRsPositie.getString(2),
									xRsPositie.getString(3),
									xRsPositie.getString(4),
									xRsPositie.getString(5),
									xRsPositie.getString(6));
								try
								{
									// add codes
									xPreCode =
										xConn.prepareStatement(
											DataBeheerDB.SELECT_KANDIDAATCODES,
											ResultSet.TYPE_FORWARD_ONLY,
											ResultSet.CONCUR_READ_ONLY);
									xPreCode.setString(1, sKieskringNr);
									xPreCode.setString(2, sKieslijstNr);
									xPreCode.setString(3, sPositieNr);
									xRsCode = xPreCode.executeQuery();
									while (xRsCode.next())
									{
										String code = xRsCode.getString(1);
										xExport.code(code);
									}
								}
								finally
								{
									xDB.closeResultSet(xRsCode);
									xDB.closePreparedStatement(xPreCode);
								}
								xExport.endPositie();
							} //end while
						}
						finally
						{
							xDB.closeResultSet(xRsPositie);
							xDB.closePreparedStatement(xPrePositie);
						}
						xExport.endKiesLijst();
					}
				}
				finally
				{
					xDB.closeResultSet(xRsKieslijst);
					xDB.closePreparedStatement(xPreKieslijst);
				}
				xExport.endKiesKring();
			}
			xExport.close();
			xConn.setAutoCommit(true);
		}
		catch (SQLException sqle)
		{
			String[] params = { "export kieslijst" };
			KOALogHelper.logErrorCode(
				"KieslijstAdminBean",
				ErrorConstants.ERR_SQL,
				params,
				sqle);
			throw new KOADataBeheerException(
				KOADataBeheerException.IO_EXCETION,
				sqle);
		}
		finally
		{
			xDB.closeResultSet(xRsKieskringen);
		}
	}
	private void createFingerprints()
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[KieslijstAdminBean.createFingerprints] Start creating the fingerprints of the kieslijst...");
		try
		{
			/* create bean interface */
			KiesLijstHome xHome = ObjectCache.getInstance().getKiesLijstHome();
			KiesLijst bean = xHome.create();
			/* create the fingerprints */
			bean.saveCurrentKieslijstFingerprints();
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[KieslijstAdminBean.createFingerprints] Kieslijst Fingerprints created...");
		}
		catch (KOAException koae)
		{
			KOALogHelper.logError(
				"KieslijstAdminBean.createFingerprints",
				"Could not create fingerprints because of KOAException",
				koae);
		}
		catch (CreateException ce)
		{
			KOALogHelper.logError(
				"KieslijstAdminBean.createFingerprints",
				"Could not create fingerprints because of Create exception",
				ce);
		}
		catch (RemoteException re)
		{
			KOALogHelper.logError(
				"KieslijstAdminBean.createFingerprints",
				"Could not create fingerprints because of Remote exception",
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
	 */
	private void checkState(int iTempID, DBUtils xDB, Connection xConn)
		throws KOAException
	{
		Hashtable htProps = new Hashtable();
		htProps.put(
			Context.INITIAL_CONTEXT_FACTORY,
			JNDIProperties.getProperty(
				JNDIProperties.CONTROLLER_CONTEXT_FACTORY));
		htProps.put(
			Context.PROVIDER_URL,
			JNDIProperties.getProperty(JNDIProperties.CONTROLLER_PROVIDER));
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
			String sCurrentState =
				ObjectCache.getInstance().getState().getCurrent_state();
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
		}
		catch (SQLException sqle)
		{
			String[] params = { "check state" };
			KOALogHelper.logErrorCode(
				"KieslijstAdminBean",
				ErrorConstants.ERR_SQL,
				params,
				sqle);
			throw new KOADataBeheerException(
				KOADataBeheerException.IO_EXCETION,
				sqle);
		}
		catch (RemoteException re)
		{
			String[] params = { "Controller" };
			KOALogHelper.logErrorCode(
				"KieslijstAdminBean",
				ErrorConstants.ERR_REMOTE,
				params,
				re);
			throw new KOADataBeheerException(
				KOADataBeheerException.EJBEXCEPTION,
				re);
		}
	}
	/**
	 * class that implement the a Sax parser
	 * it parses the data and insert is into the database 
	 * and it creates a XMLProperties list with metatdata and loggings 
	 */
	private class KieslijstParser extends DefaultHandler
	{
		private String IMPORT = "import";
		private String ACTION = "action";
		private String CONTENT_TYPE = "contenttype";
		private String META_DATA = "metadata";
		private String KIESKRING = "kieskring";
		private String KIESLIJST = "kieslijst";
		private String POSITIE = "positie";
		private String DISTRICT = "district";
		private String NUMMER = "nummer";
		private String NAAM = "naam";
		private String GROEPERING = "groepering";
		private String ACHTERNAAM = "achternaam";
		private String VOORLETTERS = "voorletters";
		private String ROEPNAAM = "roepnaam";
		private String GESLACHT = "geslacht";
		private String WOONPLAATS = "woonplaats";
		private String META_DATA_TAG = "data_metadata_";
		private String COUNT_TAG = "data_count_";
		private String INSERT_TAG = "data_insert_";
		private String IMPORT_TAG = "data_import_";
		private String NOTFOUND_TAG = "data_notfound_";
		private String NOT_INSERT_TAG = "data_notinsert_";
		private String sKieskring;
		private String sKieslijst;
		private Kieslijsten xKieslijst;
		private int iKieslijstInsert;
		private int iPositieInsert;
		private int iPositieNotInsert;
		private int iKieskringFind;
		private int iKieskring;
		private int iDistrict;
		private int iKieslijst;
		private int iPositie;
		private int iKieskringNotFound;
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
		public KieslijstParser(TempFile xTempFile)
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
				// positie tag
				else if (sQName.equals(POSITIE))
				{
					String sNummer = xAttributes.getValue(NUMMER);
					String sAchternaam = xAttributes.getValue(ACHTERNAAM);
					String sVoorletters = xAttributes.getValue(VOORLETTERS);
					String sRoepnaam = xAttributes.getValue(ROEPNAAM);
					char sGeslacht = ' ';
					if (xAttributes.getValue(GESLACHT) != "")
					{
						sGeslacht = xAttributes.getValue(GESLACHT).charAt(0);
					}
					String sWoonplaats = xAttributes.getValue(WOONPLAATS);
					iPositie++;
					// new positie
					try
					{
						if (xKieslijst != null)
						{
							insertLijstPostitie(
								xKieslijst,
								sNummer,
								sAchternaam,
								sVoorletters,
								sRoepnaam,
								sGeslacht,
								sWoonplaats);
							iPositieInsert++;
						}
						else
						{
							xWriter.writePositie(
								sNummer,
								sKieslijst,
								sKieskring,
								WrongIdWriter.NOT_FOUND_KIESKRING);
							iPositieNotInsert++;
						}
					}
					catch (KOAException ce)
					{
						iPositieNotInsert++;
						// check if a create exception
						if (ce
							.getErrorCode()
							.equals(
								KOADataBeheerException
									.CREATE_LIJSTPOS_EXCETION))
						{
							xWriter.writePositie(
								sNummer,
								sKieslijst,
								sKieskring,
								WrongIdWriter.DUBLICATE);
						}
						else
						{
							// wrap koa exception
							throw new SAXException(ce);
						}
					}
				}
				// district tag
				else if (sQName.equals(DISTRICT))
				{
					iDistrict++;
				}
				// kieslijst tag
				else if (sQName.equals(KIESLIJST))
				{
					sKieslijst = xAttributes.getValue(NUMMER);
					String sGroepering = xAttributes.getValue(GROEPERING);
					iKieslijst++;
					// new kieslijst
					try
					{
						xKieslijst =
							insertKieslijst(
								sKieskring,
								sKieslijst,
								sGroepering);
						iKieslijstInsert++;
					}
					catch (KOAException ce)
					{
						// there is no reference to the kieslijst
						xKieslijst = null;
						// check if a create exception
						if (ce
							.getErrorCode()
							.equals(KOADataBeheerException.KIESKRING_NOT_FOUND))
						{
							xWriter.writeKiesKring(
								sKieskring,
								WrongIdWriter.NOT_FOUND);
							xWriter.writeKiesLijst(
								sKieslijst,
								sKieskring,
								WrongIdWriter.NOT_FOUND_KIESKRING);
							iKieskringNotFound++;
						}
						else if (
							ce.getErrorCode().equals(
								KOADataBeheerException
									.CREATE_KIESLIJST_EXCETION))
						{
							xWriter.writeKiesLijst(
								sKieslijst,
								sKieskring,
								WrongIdWriter.DUBLICATE);
						}
						else
						{
							// wrap koa exception
							throw new SAXException(ce);
						}
					}
				}
				// kieskring tag
				else if (sQName.equals(KIESKRING))
				{
					sKieskring = xAttributes.getValue(NUMMER);
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
					COUNT_TAG + KIESKRING,
					(new Integer(iKieskring)).toString());
				xMetaProps.put(
					COUNT_TAG + DISTRICT,
					(new Integer(iDistrict)).toString());
				xMetaProps.put(
					COUNT_TAG + POSITIE,
					(new Integer(iPositie)).toString());
				xMetaProps.put(
					COUNT_TAG + KIESLIJST,
					(new Integer(iKieslijst)).toString());
				xMetaProps.put(
					INSERT_TAG + KIESLIJST,
					(new Integer(iKieslijstInsert)).toString());
				xMetaProps.put(
					INSERT_TAG + POSITIE,
					(new Integer(iPositieInsert)).toString());
				xMetaProps.put(
					NOTFOUND_TAG + KIESKRING,
					(new Integer(iKieskringNotFound)).toString());
				xMetaProps.put(
					NOT_INSERT_TAG + POSITIE,
					Integer.toString(iPositieNotInsert));
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
			return xMetaProps;
		}
	}
}