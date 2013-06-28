package com.logicacmg.koa.reportserver;
import java.sql.Connection;
import java.sql.ResultSet;
import java.sql.Statement;

import com.logicacmg.koa.constants.ErrorConstants;
import com.logicacmg.koa.constants.JNDIProperties;
import com.logicacmg.koa.db.DBUtils;
import com.logicacmg.koa.exception.KOAException;
import com.logicacmg.koa.utils.KOALogHelper;
/**
 * Collects statistics from the database to view in a statusreport
 */
public class KOAStatusReportData
{
	private static final String SELECT_KR_STATISTICS =
		"select "
			+ "(SELECT COUNT (STEMCODE) as COUNT FROM KOA01.KIEZERS) as TOTAAL_KIEZERS, "
			+ "(SELECT COUNT (STEMCODE) as COUNT FROM KOA01.KIEZERS WHERE VERWIJDERD = 'Y') as UITGESLOTEN_KIEZERS, "
			+ "(SELECT COUNT (STEMCODE) as COUNT FROM KOA01.KIEZERS WHERE REEDSGESTEMD = 'Y' and MODALITEIT = 'WEB') as AL_GESTEMD_WEB, "
			+ "(SELECT COUNT (STEMCODE) as COUNT FROM KOA01.KIEZERS WHERE REEDSGESTEMD = 'Y' and MODALITEIT = 'TEL') as AL_GESTEMD_TEL, "
			+ "(SELECT COUNT (STEMCODE) as COUNT FROM KOA01.KIEZERS WHERE ACCOUNTLOCKED = 'Y' and TIMESTAMPUNLOCK > (CURRENT TIMESTAMP) and VERWIJDERD != 'Y') as GEBLOKKEERDE_KIEZERS "
			+ "FROM sysibm.sysdummy1 FETCH FIRST 1 ROWS ONLY";
	private static final String SELECT_ESB_STATISTICS =
		"SELECT count(STEMNUMMER) as ESB_STEMMEN FROM KOA01.ENCRYPTEDESB "
			+ "FETCH FIRST 1 ROWS ONLY";
	private int totaalKiezers = 0;
	private int uitgeslotenKiezers = 0;
	private int alGestemdWeb = 0;
	private int alGestemdTel = 0;
	private int geblokkeerdeKiezers = 0;
	private int esbStemmen = 0;
	/**
	 * Constructor for the KOAStatusReportData
	 */
	public KOAStatusReportData()
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[KOAStatusReportData] constructing the KOAStatusReportData");
		try
		{
			/* set up the utility classes for the KR and ESB database */
			DBUtils xDBKR =
				new DBUtils(
					JNDIProperties.getProperty(
						JNDIProperties.DATASOURCE_KR_NO_TRANS));
			DBUtils xDBESB =
				new DBUtils(
					JNDIProperties.getProperty(
						JNDIProperties.DATASOURCE_ESB_NO_TRANS));
			/* get connection and statement for the KR database */
			Connection connKR = xDBKR.getConnection();
			Statement stmtKRStatistics = connKR.createStatement();
			/* get connection and statement for the ESB database */
			Connection connESB = xDBESB.getConnection();
			Statement stmtESBStatistics = connESB.createStatement();
			/* execute the queries on the KR and ESB databases */
			ResultSet rstKRStatistics =
				xDBKR.executeResultQuery(
					stmtKRStatistics,
					SELECT_KR_STATISTICS);
			ResultSet rstESBStatistics =
				xDBESB.executeResultQuery(
					stmtESBStatistics,
					SELECT_ESB_STATISTICS);
			if (rstKRStatistics.next() == true)
			{
				totaalKiezers = rstKRStatistics.getInt("TOTAAL_KIEZERS");
				uitgeslotenKiezers =
					rstKRStatistics.getInt("UITGESLOTEN_KIEZERS");
				alGestemdWeb = rstKRStatistics.getInt("AL_GESTEMD_WEB");
				alGestemdTel = rstKRStatistics.getInt("AL_GESTEMD_TEL");
				geblokkeerdeKiezers =
					rstKRStatistics.getInt("GEBLOKKEERDE_KIEZERS");
			}
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[KOAStatusReportData] totaal kiezers :" + totaalKiezers);
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[KOAStatusReportData] uitgesloten kiezers :"
					+ uitgeslotenKiezers);
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[KOAStatusReportData] al gestemd web :" + alGestemdWeb);
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[KOAStatusReportData] al gestemd tel :" + alGestemdTel);
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[KOAStatusReportData] geblokkeerde kiezers :"
					+ geblokkeerdeKiezers);
			if (rstESBStatistics.next() == true)
			{
				esbStemmen = rstESBStatistics.getInt("ESB_STEMMEN");
			}
			KOALogHelper.log(
				KOALogHelper.TRACE,
				"[KOAStatusReportData] aantal stemmen in de esb :"
					+ esbStemmen);
			/* close everything */
			rstKRStatistics.close();
			rstESBStatistics.close();
			stmtKRStatistics.close();
			stmtESBStatistics.close();
			connKR.close();
			connESB.close();
		}
		catch (KOAException koae)
		{
			KOALogHelper.logError(
				"KOAStatusReportData",
				"KOA Exception during construction of the KOAStatusReportData",
				koae);
		}
		catch (Exception e)
		{
			KOALogHelper.logErrorCode(
				"KOAStatusReportData",
				ErrorConstants.ERR_READER_INIT,
				e);
		}
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[KOAStatusReportData] KOAStatusReportData constructed...");
	}
	/**
	 * @return int the total number of voters
	 */
	public int getTotaalKiezers()
	{
		return totaalKiezers;
	}
	/**
	 * @return int the number of voters who are excluded from voting
	 */
	public int getUitgeslotenKiezers()
	{
		return uitgeslotenKiezers;
	}
	/**
	 * @return int the number of voters who have voted through the web interface
	 */
	public int getAlGestemdWeb()
	{
		return alGestemdWeb;
	}
	/**
	 * @return int the number of voters who have voted through the telephony interface
	 */
	public int getAlGestemdTel()
	{
		return alGestemdTel;
	}
	/**
	 * @return int the number of voters who are temporarily blocked 
	 */
	public int getGeblokkeerdeKiezers()
	{
		return geblokkeerdeKiezers;
	}
	/**
	 * @return int the number of votes in the electronic ballot box
	 */
	public int getESBStemmen()
	{
		return esbStemmen;
	}
}