/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.databeheer.bean.KieslijstUpload.java
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
package com.logicacmg.koa.databeheer.command;
import java.io.IOException;
import java.io.InputStream;
import java.rmi.RemoteException;
import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;
import java.sql.Timestamp;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;

import javax.naming.Context;
import javax.naming.InitialContext;
import javax.naming.NamingException;

import org.xml.sax.InputSource;
import org.xml.sax.SAXException;
import org.xml.sax.SAXParseException;
import org.xml.sax.XMLReader;
import org.xml.sax.helpers.XMLReaderFactory;

import com.logica.eplatform.command.AbstractTargetableCommand;
import com.logica.eplatform.command.CommandException;
import com.logica.eplatform.command.http.HttpCommand;
import com.logica.eplatform.error.EPlatformException;
import com.logica.eplatform.util.LogHelper;
import com.logicacmg.koa.constants.ErrorConstants;
import com.logicacmg.koa.constants.FunctionalProps;
import com.logicacmg.koa.constants.JNDIProperties;
import com.logicacmg.koa.constants.SystemState;
import com.logicacmg.koa.constants.TechnicalProps;
import com.logicacmg.koa.controller.beans.Controller;
import com.logicacmg.koa.controller.beans.ControllerHome;
import com.logicacmg.koa.databeheer.command.CommandConstants;
import com.logicacmg.koa.databeheer.xml.SAXErrorHandler;
import com.logicacmg.koa.databeheer.xml.Validator;
import com.logicacmg.koa.db.DBUtils;
import com.logicacmg.koa.db.DataBeheerDB;
import com.logicacmg.koa.eventhandling.AuditEventListener;
import com.logicacmg.koa.exception.KOADataBeheerException;
import com.logicacmg.koa.exception.KOAException;
import com.logicacmg.koa.utils.KOALogHelper;
/**
 * This class is the command class for the 4 uploads files
 * (for 3 kiesregister files and 1 kieslijst file). 
 * It controls the upload and validates the xml files.
 * If the validation succeed the xml file will be stored in the
 * database.
 */
public class Upload extends AbstractTargetableCommand implements HttpCommand
{
	// const. values	
	private String UPLOAD = "upload";
	// private members
	private Map xMap;
	private int iTempDataID;
	// the upload file
	private transient FileItem xFile;
	private String sUri;
	private static Map xStateMapping;
	private static Map xXsdMapping;
	private static Map xTextMapping;
	private String sCurrentState;
	// this code wil be executed at class loading
	static {
		xStateMapping = new TreeMap();
		xStateMapping.put(
			"/UploadKieslijst",
			new String[] { SystemState.PREPARE });
		xStateMapping.put(
			"/UploadKRRemove",
			new String[] { SystemState.OPEN, SystemState.PREPARE });
		xStateMapping.put(
			"/UploadKRUpdate",
			new String[] { SystemState.OPEN, SystemState.PREPARE });
		xStateMapping.put(
			"/UploadKRReplace",
			new String[] { SystemState.PREPARE });
		xXsdMapping = new TreeMap();
		xXsdMapping.put("/UploadKieslijst", "/kieslijst.xsd");
		xXsdMapping.put("/UploadKRRemove", "/krremove.xsd");
		xXsdMapping.put("/UploadKRUpdate", "/krreplaceupdate.xsd");
		xXsdMapping.put("/UploadKRReplace", "/krreplaceupdate.xsd");
		xTextMapping = new TreeMap();
		xTextMapping.put("/UploadKieslijst", "inlezen van kandidaatlijsten");
		xTextMapping.put("/UploadKRRemove", "verwijderen van kiezers");
		xTextMapping.put("/UploadKRUpdate", "toevoegen van kiezers");
		xTextMapping.put("/UploadKRReplace", "vervangen van kiezers");
	}
	/**
	 * Not used
	 * @see AbstractTargetableCommand#execute()
	 */
	public void execute() throws CommandException, EPlatformException
	{
	}
	/**
	 * Not used
	 * @see HttpCommand#getErrorJSP()
	 */
	public String getErrorJSP()
	{
		return "error.jsp";
	}
	/**
	 * @see HttpCommand#getResultJSP()
	 */
	public String getResultJSP()
	{
		return "result.jsp";
	}
	/**
	 * Returns a map with the result of valiation 
	 * The infomation in the map is viewed in the retult jsp page
	 * It contains the metadata tags the attributes of the import tag
	 * and the rows counted in the file
	 * 
	 * @return map with the result of valiation 
	 */
	public Map getResult()
	{
		return xMap;
	}
	/**
	 * The init methode uses the HttpServletRequest to get the upload file.
	 * @see HttpCommand#init(HttpServletRequest)
	 * 
	 * @param xReq The HttpServletRequest with the upload file
	 */
	public void init(HttpServletRequest xReq) throws EPlatformException
	{
		//try {
		KOALogHelper.log(LogHelper.INFO, "[Upload] Upload started");
		sUri = xReq.getServletPath();
		String sAction = (String) xTextMapping.get(sUri);
		KOALogHelper.audit(
			KOALogHelper.INFO,
			AuditEventListener.DATA_MANAGEMENT,
			"Upload",
			xReq.getUserPrincipal().getName(),
			"Het uploaden van het geselecteerde bestand met actie '"
				+ sAction
				+ "' is gestart.");
		Iterator xIter = getFileItem(xReq);
		FileItem xTemp = null;
		// get the right param
		while (xIter.hasNext())
		{
			xTemp = (FileItem) xIter.next();
			if (xTemp.getFieldName().equals(UPLOAD))
			{
				xFile = xTemp;
			}
		}
	}
	/**
	 * This method is (localy) executed before a command is (remotely) executed
	 * it validates the xml upload file and stores the file in the database if the
	 * valiadation was correct.
	 * 
		 */
	public void preExecution() throws EPlatformException
	{
		try
		{
			// check the state of the system
			checkState(sUri);
			KOALogHelper.log(LogHelper.INFO, "[Upload] Check state OK");
			if (xFile.getSize() == 0)
			{
				KOALogHelper.log(
					LogHelper.ERROR,
					"[Upload] Upload param not found");
				// param is not found in the request
				throw new KOADataBeheerException(
					KOADataBeheerException.UPLOAD_PARAM_NOT_FOUND);
			}
			KOALogHelper.log(LogHelper.INFO, "[Upload] Upload param OK");
			xMap =
				parseXML(
					xFile.getInputStream(),
					(String) xXsdMapping.get(sUri));
			KOALogHelper.log(LogHelper.INFO, "[Upload] Upload parsen OK");
			checkReport(xMap);
			KOALogHelper.log(LogHelper.INFO, "[Upload] Check report OK");
			KOALogHelper.log(
				LogHelper.INFO,
				"[Upload] " + xFile.getStoreLocation() + "," + xFile.getName());
			storeUpload(xFile.getInputStream(), (int) xFile.getSize(), xMap);
			KOALogHelper.log(LogHelper.INFO, "[Upload] Store upload OK");
		}
		catch (IOException ioe)
		{
			String[] params = { "Upload file" };
			KOALogHelper.logErrorCode(
				"Upload",
				ErrorConstants.ERR_IO,
				params,
				ioe);
			throw new KOADataBeheerException(
				KOADataBeheerException.IO_EXCETION,
				ioe);
		}
	}
	/**
	 * Stores 3 Attributes in het session these attributes will be used 
	 * in the ProcessUpload command.
	 * The ID (primary key) of the tempdata table
	 * The action of the xml file
	 * The contenttype of the 
	 * @see HttpCommand#updateSession(HttpSession)
	 * 
	 * @param xSession The session.
	 */
	public void updateSession(HttpSession xSession) throws EPlatformException
	{
		// add values to the session
		xSession.setAttribute(
			CommandConstants.UPLOAD_SESSION,
			(new Integer(iTempDataID)).toString());
		xSession.setAttribute(
			CommandConstants.UPLOAD_ACTION,
			xMap.get(CommandConstants.UPLOAD_ACTION));
		xSession.setAttribute(
			CommandConstants.UPLOAD_CONTENTTYPE,
			xMap.get(CommandConstants.UPLOAD_CONTENTTYPE));
	}
	/**
	 * This methode gets the upload file from the HttpServletRequest
	 * 
	 * @param xReq the HttpServletRequest whit the upload file
	 * @return Iterator a list white al the items (FileItem) from xReq
	 */
	private Iterator getFileItem(HttpServletRequest xReq) throws KOAException
	{
		try
		{
			FileUpload xFu = new FileUpload();
			// maximum size before a FileUploadException will be thrown
			xFu.setSizeMax(100000000);
			// maximum size that will be stored in memory
			xFu.setSizeThreshold(4096);
			// the location for saving data that is larger than getSizeThreshold()
			xFu.setRepositoryPath(
				TechnicalProps.getProperty(TechnicalProps.TEMPDIR_UPLOAD));
			List xFileItems = xFu.parseRequest(xReq);
			// assume we know there are two files. The first file is a small 
			// text file, the second is unknown and is written to a file on
			// the server 
			return xFileItems.iterator();
		}
		catch (FileUploadException fue)
		{
			KOALogHelper.logErrorCode(
				"Upload",
				ErrorConstants.ERR_FILE_UPLOAD,
				fue);
			throw new KOADataBeheerException(
				KOADataBeheerException.UPLOAD_EXCEPTION,
				fue);
		}
	}
	/**
	 * This methode stores the upload file in the database
	 * 
	 * @param xIn stream containing the file
	 * @param size The size of the upload file
	 * @param map the map with the reporst items
	 * @return Iterator a list white al the items (FileItem) from xReq
	 */
	private void storeUpload(InputStream xIn, int size, Map map)
		throws KOAException
	{
		Connection xConn = null;
		ResultSet xRS = null;
		PreparedStatement xPre = null;
		// database
		DBUtils xDB =
			new DBUtils(
				JNDIProperties.getProperty(
					JNDIProperties.DATASOURCE_KOA_NO_TRANS));
		try
		{
			// get connection
			xConn = xDB.getConnection();
			xConn.setAutoCommit(true);
			Statement xStmt = xConn.createStatement();
			KOALogHelper.log(LogHelper.INFO, "[Upload] Get new tempdata id");
			xRS =
				xDB.executeResultQuery(
					xStmt,
					DataBeheerDB.SELECT_MAX_ID_TEMP_DATA);
			xRS.next();
			iTempDataID = xRS.getInt(1);
			iTempDataID++;
			xRS.close();
			xStmt.close();
			KOALogHelper.log(LogHelper.INFO, "[Upload] Close connection");
			xConn.close();
			KOALogHelper.log(LogHelper.INFO, "[Upload] Create connection");
			xConn = xDB.getConnection();
			KOALogHelper.log(LogHelper.INFO, "[Upload] Set autocommit");
			xConn.setAutoCommit(false);
			// store upload in database
			KOALogHelper.log(LogHelper.INFO, "[Upload] Prepare statement");
			xPre = xConn.prepareStatement(DataBeheerDB.INSERT_TEMP_DATA);
			KOALogHelper.log(LogHelper.INFO, "[Upload] Set id");
			xPre.setInt(1, iTempDataID);
			KOALogHelper.log(LogHelper.INFO, "[Upload] Set action");
			xPre.setString(2, (String) map.get(CommandConstants.UPLOAD_ACTION));
			KOALogHelper.log(LogHelper.INFO, "[Upload] Set content type");
			xPre.setString(
				3,
				(String) map.get(CommandConstants.UPLOAD_CONTENTTYPE));
			xPre.setTimestamp(4, new Timestamp(System.currentTimeMillis()));
			KOALogHelper.log(LogHelper.INFO, "[Upload] Set binary stream");
			xPre.setBinaryStream(5, xIn, size);
			KOALogHelper.log(LogHelper.INFO, "[Upload] Execute update");
			xPre.executeUpdate();
			KOALogHelper.log(LogHelper.INFO, "[Upload] Commit");
			xConn.commit();
		}
		catch (SQLException qsle)
		{
			String[] params = { "Inserting Temp date information" };
			KOALogHelper.logErrorCode(
				"Upload",
				ErrorConstants.ERR_SQL,
				params,
				qsle);
			throw new KOADataBeheerException(
				KOADataBeheerException.STORE_UPLOAD,
				qsle);
		}
		finally
		{
			xDB.closeResultSet(xRS);
			xDB.closePreparedStatement(xPre);
			xDB.closeConnection(xConn);
		}
	}
	/**
	 * This methode validates the upload file (xml file) 
	 * 
	 * @param xIn stream containing the file
	 * @param sXsd the position of the xsd file
	 * @return Map the map with the report items.
	 */
	private Map parseXML(InputStream xIn, String sXsd)
		throws KOADataBeheerException
	{
		try
		{
			XMLReader xXMLReader =
				XMLReaderFactory.createXMLReader(
					"org.apache.xerces.parsers.SAXParser");
			InputSource xInSource = new InputSource(xIn);
			xInSource.setEncoding(
				TechnicalProps.getProperty(TechnicalProps.XML_ENCODING));
			// settings for using validation en no namespasing
			xXMLReader.setFeature(
				"http://apache.org/xml/features/validation/schema",
				true);
			xXMLReader.setFeature(
				"http://xml.org/sax/features/validation",
				true);
			xXMLReader.setFeature(
				"http://apache.org/xml/features/validation/schema-full-checking",
				true);
			xXMLReader.setProperty(
				"http://apache.org/xml/properties/schema/external-noNamespaceSchemaLocation",
				getClass().getResource(sXsd).toString());
			xXMLReader.setErrorHandler(new SAXErrorHandler());
			Validator val = new Validator();
			xXMLReader.setContentHandler(val);
			xXMLReader.parse(xInSource);
			/* Here we need to check if the filetype is allowed
			   for this systems state */
			if (sUri.equals("/UploadKieslijst")
				&& !(val
					.getMetaData()
					.get(Validator.ACTION)
					.equals(
						FunctionalProps.getProperty(
							FunctionalProps.IMPORT_REPLACE))))
			{
				throw new KOADataBeheerException(
					ErrorConstants.ERR_IMPORT_INCORRECT_ACTION);
			}
			if (sUri.equals("/UploadKRRemove")
				&& !(val
					.getMetaData()
					.get(Validator.ACTION)
					.equals(
						FunctionalProps.getProperty(
							FunctionalProps.IMPORT_DELETE))))
			{
				throw new KOADataBeheerException(
					ErrorConstants.ERR_IMPORT_INCORRECT_ACTION);
			}
			if (sUri.equals("/UploadKRUpdate")
				&& !(val
					.getMetaData()
					.get(Validator.ACTION)
					.equals(
						FunctionalProps.getProperty(
							FunctionalProps.IMPORT_APPEND))))
			{
				throw new KOADataBeheerException(
					ErrorConstants.ERR_IMPORT_INCORRECT_ACTION);
			}
			if (sUri.equals("/UploadKRReplace")
				&& !(val
					.getMetaData()
					.get(Validator.ACTION)
					.equals(
						FunctionalProps.getProperty(
							FunctionalProps.IMPORT_REPLACE))))
			{
				throw new KOADataBeheerException(
					ErrorConstants.ERR_IMPORT_INCORRECT_ACTION);
			}
			return val.getMetaData();
		}
		catch (SAXParseException saxpe)
		{
			String[] params = { Integer.toString(saxpe.getLineNumber())};
			KOALogHelper.logErrorCode(
				"[Upload]",
				ErrorConstants.ERR_SAX_PARSE_EXCEPTION,
				params,
				saxpe);
			throw new KOADataBeheerException(
				KOADataBeheerException.UPLOAD_PARSE_XML,
				new String[] { "" + saxpe.getLineNumber()},
				saxpe);
		}
		catch (SAXException saxe)
		{
			KOALogHelper.logErrorCode(
				"[Upload]",
				ErrorConstants.ERR_SAX_EXCEPTION,
				saxe);
			throw new KOADataBeheerException(
				KOADataBeheerException.UPLOAD_SAX_XML,
				saxe);
		}
		catch (java.io.IOException ioe)
		{
			KOALogHelper.logError("[Upload]", "IOException", ioe);
			throw new KOADataBeheerException(
				KOADataBeheerException.UPLOAD_PARSE_XML,
				ioe);
		}
		catch (KOAException koae)
		{
			throw new KOADataBeheerException(koae.getErrorCode());
		}
	}
	/**
	 *  This methode checks the state and trows a exception if the 
	 *  state is not correct
	 * 
	 * @param sUri servlet path
	 */
	private void checkState(String sUri) throws KOAException
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
			InitialContext ic = new InitialContext(htProps);
			Object obj =
				ic.lookup(
					JNDIProperties.getProperty(JNDIProperties.CONTROLLER_NAME));
			ControllerHome home =
				(ControllerHome) javax.rmi.PortableRemoteObject.narrow(
					obj,
					ControllerHome.class);
			Controller controller = home.create();
			sCurrentState = controller.getCurrentState();
			String[] saState = (String[]) xStateMapping.get(sUri);
			Iterator xKeySet = xStateMapping.keySet().iterator();
			KOALogHelper.log(
				LogHelper.INFO,
				"[Upload] Upload state = " + sCurrentState);
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
					KOADataBeheerException.WRONG_STATE,
					new String[] {
						SystemState.getDutchTranslationForState(
							sCurrentState)});
			}
		}
		catch (NamingException ne)
		{
			String[] params = { "Controller" };
			KOALogHelper.logErrorCode(
				"[Upload]",
				ErrorConstants.ERR_NAMING,
				params,
				ne);
			throw new KOADataBeheerException(
				KOADataBeheerException.EJBEXCEPTION,
				ne);
		}
		catch (RemoteException re)
		{
			String[] params = { "Controller" };
			KOALogHelper.logErrorCode(
				"[Upload]",
				ErrorConstants.ERR_REMOTE,
				params,
				re);
			throw new KOADataBeheerException(
				KOADataBeheerException.EJBEXCEPTION,
				re);
		}
		catch (CreateException ce)
		{
			String[] params = { "Controller" };
			KOALogHelper.logErrorCode(
				"[Upload]",
				ErrorConstants.ERR_CREATE,
				params,
				ce);
			throw new KOADataBeheerException(
				KOADataBeheerException.EJBEXCEPTION,
				ce);
		}
	}
	/**
	 * Check if the file header (metadata tag) has the same count as the tag in the
	 * xml file
	 * 
	 * @param xReport the report from the xml parsing
	 * @throws KOAException If the count is net equal
	 */
	public void checkReport(Map xReport) throws KOAException
	{
		String sType =
			(String) xReport.get(CommandConstants.UPLOAD_CONTENTTYPE);
		String sAction = (String) xReport.get(CommandConstants.UPLOAD_ACTION);
		if (sType.equals(CommandConstants.UPLOAD_KIESLIJST))
		{
			String sStr =
				(String) xReport.get(CommandConstants.UPLOAD_KIESKRING);
			String sCount =
				(String) xReport.get(CommandConstants.UPLOAD_KIESKRING_COUNT);
			if (!sStr.equals(sCount))
			{
				KOALogHelper.log(
					LogHelper.ERROR,
					"[Upload] Header amount is not equal to the content ("
						+ CommandConstants.UPLOAD_KIESKRING_COUNT
						+ ")");
				throw new KOADataBeheerException(
					KOADataBeheerException.WRONG_REPORT,
					new String[] {
						CommandConstants.UPLOAD_KIESKRING,
						sStr,
						CommandConstants.UPLOAD_KIESKRING_COUNT,
						sCount });
			}
			sStr = (String) xReport.get(CommandConstants.UPLOAD_DISTRICT);
			sCount =
				(String) xReport.get(CommandConstants.UPLOAD_DISTRICT_COUNT);
			if (!sStr.equals(sCount))
			{
				KOALogHelper.log(
					LogHelper.ERROR,
					"[Upload] Header amount is not equal to the content ("
						+ CommandConstants.UPLOAD_DISTRICT_COUNT
						+ ")");
				throw new KOADataBeheerException(
					KOADataBeheerException.WRONG_REPORT,
					new String[] {
						CommandConstants.UPLOAD_DISTRICT,
						sStr,
						CommandConstants.UPLOAD_DISTRICT_COUNT,
						sCount });
			}
			sStr = (String) xReport.get(CommandConstants.UPLOAD_KIESLIJST);
			sCount =
				(String) xReport.get(CommandConstants.UPLOAD_KIESLIJST_COUNT);
			if (!sStr.equals(sCount))
			{
				KOALogHelper.log(
					LogHelper.ERROR,
					"[Upload] Header amount is not equal to the content ("
						+ CommandConstants.UPLOAD_KIESLIJST_COUNT
						+ ")");
				throw new KOADataBeheerException(
					KOADataBeheerException.WRONG_REPORT,
					new String[] {
						CommandConstants.UPLOAD_KIESLIJST,
						sStr,
						CommandConstants.UPLOAD_KIESLIJST_COUNT,
						sCount });
			}
			sStr = (String) xReport.get(CommandConstants.UPLOAD_POSITIE);
			sCount =
				(String) xReport.get(CommandConstants.UPLOAD_POSITIE_COUNT);
			if (!sStr.equals(sCount))
			{
				KOALogHelper.log(
					LogHelper.ERROR,
					"[Upload] Header amount is not equal to the content ("
						+ CommandConstants.UPLOAD_POSITIE_COUNT
						+ ")");
				throw new KOADataBeheerException(
					KOADataBeheerException.WRONG_REPORT,
					new String[] {
						CommandConstants.UPLOAD_POSITIE,
						sStr,
						CommandConstants.UPLOAD_POSITIE_COUNT,
						sCount });
			}
		}
		else
		{
			String sKiezer =
				(String) xReport.get(CommandConstants.UPLOAD_KIEZER);
			String sKiezerCount =
				(String) xReport.get(CommandConstants.UPLOAD_KIEZER_COUNT);
			if (!sKiezer.equals(sKiezerCount))
			{
				KOALogHelper.log(
					LogHelper.ERROR,
					"[Upload] Header amount is not equal to the content ("
						+ CommandConstants.UPLOAD_KIEZER_COUNT
						+ ")");
				throw new KOADataBeheerException(
					KOADataBeheerException.WRONG_REPORT,
					new String[] {
						CommandConstants.UPLOAD_KIEZER,
						sKiezer,
						CommandConstants.UPLOAD_KIEZER_COUNT,
						sKiezerCount });
			}
		}
	}
}