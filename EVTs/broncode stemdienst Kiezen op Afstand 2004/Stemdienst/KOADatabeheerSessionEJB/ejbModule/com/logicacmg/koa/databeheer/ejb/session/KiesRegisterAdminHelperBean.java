/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.databeheer.ejb.session.KiesRegisterAdminHelperBean.java
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
import java.rmi.RemoteException;
import java.util.ArrayList;
import java.util.Enumeration;
import java.util.Hashtable;

import com.logicacmg.koa.constants.ErrorConstants;
import com.logicacmg.koa.databeheer.data.KiezerData;
import com.logicacmg.koa.databeheer.xml.WrongIdWriter;
import com.logicacmg.koa.exception.KOADataBeheerException;
import com.logicacmg.koa.exception.KOAException;
import com.logicacmg.koa.koaschema.Districten;
import com.logicacmg.koa.koaschema.DistrictenHome;
import com.logicacmg.koa.koaschema.DistrictenKey;
import com.logicacmg.koa.koaschema.KieskringenKey;
import com.logicacmg.koa.kr.beans.Kiezers;
import com.logicacmg.koa.kr.beans.KiezersHome;
import com.logicacmg.koa.sar.Sar;
import com.logicacmg.koa.sar.SarHome;
import com.logicacmg.koa.sar.SarKey;
import com.logicacmg.koa.security.RandomGenerator;
import com.logicacmg.koa.utils.KOALogHelper;
import com.logicacmg.koa.utils.ObjectCache;
/**
 * Bean implementation class for Enterprise Bean: KiesRegisterAdminHelper
 * 
 * This bean is a helper bean for the KiesRegisterAdminBean and takes care
 * of al the methodes that needs "requersNew" transaction
 * inserting of list of kiezers
 * updating of list of kiezers
 * remove of kiezer
 */
public class KiesRegisterAdminHelperBean implements javax.ejb.SessionBean
{
	private javax.ejb.SessionContext mySessionCtx;
	private Hashtable htDistrictKieskring;
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
		htDistrictKieskring = new Hashtable();
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
	 * insert a list of kiezers in the database
	 * 
	 * @param xKiezers List of kiezers 
	 * @param xKiezersHome reference to kiezers home interface (this is for performance resons)
	 * @param xSarHome reference to sar home interface (this is for performance resons)
	 * @return String[] Array of kiezers id's that are already in the kiezers table
	 */
	public String[] insertKiezers(
		KiezerData[] xKiezers,
		KiezersHome xKiezersHome,
		SarHome xSarHome)
		throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[KiesRegisterAdminHelperBean.insertKiezers] calling insertKiezers()");
		long now = System.currentTimeMillis();
		RandomGenerator xGenerator = RandomGenerator.getInstance();
		long now2 = System.currentTimeMillis();
		int nrOfKiezers = xKiezers.length;
		ArrayList xWrongkeys = new ArrayList();
		try
		{
			String sStemcode = null;
			String sTxCode = null;
			for (int i = 0; i < xKiezers.length; i++)
			{
				try
				{
					// if kiezer is already inserted in kiezer table
					xKiezersHome.findByKiezerId(xKiezers[i].getKiezer());
					// kiezer is found log as an error
					xWrongkeys.add(xKiezers[i].getKiezer());
				}
				catch (FinderException finderE)
				{
					// KOALogHelper.log(KOALogHelper.TRACE, "calling confimDistrictKRngComboExists()");
					//Confirm the Kiesring and District exist and are linked in the db
					if (confimDistrictKRngComboExists(xKiezers[i].getDistrict(),
						xKiezers[i].getKieskring()))
					{
						// KOALogHelper.log(KOALogHelper.TRACE, "confimDistrictKRngComboExists() returns true so record will be processed");
						//Combination is in the db so continue
						try
						{
							// find if kiezer has allready a stemcode in SAR table
							Sar xSar =
								xSarHome.findByPrimaryKey(
									new SarKey(xKiezers[i].getKiezer()));
							sStemcode = xSar.getStemcode();
						}
						catch (FinderException fe)
						{
							// create a new stemcode 
							boolean bCodeUniek = false;
							while (!bCodeUniek)
							{
								try
								{
									sStemcode = xGenerator.getKiezersCode();
									// store stem code								
									xSarHome.create(
										xKiezers[i].getKiezer(),
										sStemcode);
									// stemcode does not exist 
									bCodeUniek = true;
								}
								catch (CreateException fde)
								{
									// stemcode does not exist 
									KOALogHelper.log(
										KOALogHelper.INFO,
										"[KiesRegisterAdminHelperBean] Duplicate KiezersCode");
								}
							}
						}
						try
						{
							sTxCode = "";
							// insert kiezer					
							xKiezersHome.create(
								sStemcode,
								xKiezers[i].getKiezer(),
								xKiezers[i].getHashedWW(),
								xKiezers[i].getDistrict(),
								xKiezers[i].getKieskring(),
								sTxCode);
						}
						catch (CreateException ce)
						{
							KOALogHelper.log(
								KOALogHelper.INFO,
								"[KiesRegisterAdminHelperBean] Duplicate TransactieCode");
						}
					}
					else
					{
						KOALogHelper.log(
							KOALogHelper.TRACE,
							"confimDistrictKRngComboExists() returns false so will not process the record");
						//District,Kieskring combo not found in the db
						//dont process and add to the errors
						xWrongkeys.add(xKiezers[i].getKiezer());
					}
				} //catch				
			} // for 
		}
		catch (RemoteException ne)
		{
			String[] params = { "Kiezers" };
			KOALogHelper.logErrorCode(
				"KiesRegisterAdminHelperBean",
				ErrorConstants.ERR_REMOTE,
				params,
				ne);
			throw new KOADataBeheerException(
				KOADataBeheerException.EJBEXCEPTION,
				ne);
		}
		// return the wrong kiezers id's
		long now3 = System.currentTimeMillis();
		long insertgroup = (now3 - now2) / 1000;
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[KiesRegisterAdminHelperBean.insertKiezers] Insert "
				+ nrOfKiezers
				+ " kiezers time in seconds: "
				+ insertgroup);
		return (String[]) xWrongkeys.toArray(new String[xWrongkeys.size()]);
	}
	/**
	 * update a list of kiezers in the database
	 * 
	 * @param xKiezers List of kiezers 
	 * @param xKiezersHome reference to kiezers home interface (this is for performance resons)
	 * @param xSarHome reference to sar home interface (this is for performance resons)
	 * @return String[] Array of kiezers id's that are already in the kiezers table
	 */
	public String[] updateKiezers(
		KiezerData[] xKiezers,
		KiezersHome xKiezersHome,
		SarHome xSarHome)
		throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[KiesRegisterAdminHelperBean.updateKiezers] Entering updateKiezers()");
		RandomGenerator xGenerator = RandomGenerator.getInstance();
		ArrayList xWrongkeys = new ArrayList();
		try
		{
			String sStemcode = null;
			String sTxCode = null;
			for (int i = 0; i < xKiezers.length; i++)
			{
				try
				{
					// if kiezer is already inserted in kiezer table
					Kiezers xKiezer =
						xKiezersHome.findByKiezerId(xKiezers[i].getKiezer());
					// if already removed
					if (xKiezer.getVerwijderd().booleanValue())
					{
						xKiezer.setVerwijderd(new Boolean(false));
					}
					else
					{
						// kiezer is alread known in the system
						xWrongkeys.add(xKiezers[i].getKiezer());
					}
				}
				catch (FinderException finderE)
				{
					//Confirm the Kiesring and District exist and are linked in the db
					if (confimDistrictKRngComboExists(xKiezers[i].getDistrict(),
						xKiezers[i].getKieskring()))
					{
						try
						{
							// find if kiezer has allready a stemcode in SAR table
							Sar xSar =
								xSarHome.findByPrimaryKey(
									new SarKey(xKiezers[i].getKiezer()));
							sStemcode = xSar.getStemcode();
						}
						catch (FinderException fe)
						{
							// create a new stemcode 
							boolean bCodeUniek = false;
							while (!bCodeUniek)
							{
								try
								{
									sStemcode = xGenerator.getKiezersCode();
									// store stem code								
									xSarHome.create(
										xKiezers[i].getKiezer(),
										sStemcode);
									// stemcode does not exist 
									bCodeUniek = true;
								}
								catch (CreateException fde)
								{
									KOALogHelper.log(
										KOALogHelper.INFO,
										"[KiesRegisterAdminHelperBean] Duplicate KiezersCode");
								}
							}
						}
						try
						{
							sTxCode = "";
							// insert kiezer					
							xKiezersHome.create(
								sStemcode,
								xKiezers[i].getKiezer(),
								xKiezers[i].getHashedWW(),
								xKiezers[i].getDistrict(),
								xKiezers[i].getKieskring(),
								sTxCode);
						}
						catch (CreateException ce)
						{
							KOALogHelper.log(
								KOALogHelper.ERROR,
								"[KiesRegisterAdminHelperBean] Failed to create kiezer");
							throw new KOADataBeheerException(
								KOADataBeheerException.EJBEXCEPTION,
								ce);
						}
					}
					else
					{
						//District,Kieskring combo not found in the db
						//dont process and add to the errors
						xWrongkeys.add(xKiezers[i].getKiezer());
					} //if
				} //catch				
			} // for 
		}
		catch (RemoteException ne)
		{
			String[] params = { "SAR" };
			KOALogHelper.logErrorCode(
				"KiesRegisterAdminHelperBean",
				ErrorConstants.ERR_REMOTE,
				params,
				ne);
			throw new KOADataBeheerException(
				KOADataBeheerException.EJBEXCEPTION,
				ne);
		}
		// return the wrong kiezers id's
		return (String[]) xWrongkeys.toArray(new String[xWrongkeys.size()]);
	}
	/**
	 * Set the flag kiezer removed in the database
	 * 
	 * @param sKiezerId kiezerID
	 * @return String returns null if OK else it returns the reason why its is not removed
	 */
	public String removeKiezer(String sKiezerId) throws KOAException
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[KiesRegisterAdminHelperBean.removeKiezer] Entering removeKiezer()");
		try
		{
			KiezersHome xKiezersHome =
				ObjectCache.getInstance().getKiezersHome();
			try
			{
				// if kiezer is already in kiezer table
				Kiezers xKiezer = xKiezersHome.findByKiezerId(sKiezerId);
				// if already removed
				if (xKiezer.getVerwijderd().booleanValue())
				{
					// kiezer is already removed
					return WrongIdWriter.IS_REMOVED;
				}
				if (xKiezer.getReedsgestemd().booleanValue())
				{
					// kiezer has voted
					return WrongIdWriter.HAS_VOTED;
				}
				else
				{
					// set verwijderd flag
					xKiezer.setVerwijderd(new Boolean(true));
				}
			}
			catch (FinderException finderE)
			{
				// unknown kiezer
				return WrongIdWriter.UNKNOWN_KIEZER;
			}
		}
		catch (RemoteException ne)
		{
			String[] params = { "Kiezer" };
			KOALogHelper.logErrorCode(
				"KiesRegisterAdminHelperBean",
				ErrorConstants.ERR_REMOTE,
				params,
				ne);
			throw new KOADataBeheerException(
				KOADataBeheerException.EJBEXCEPTION,
				ne);
		}
		return null;
	}
	/**
	 * Confirm the Kiesring has a District
	 * 
	 * @param sKiezerId kiezerID
	 * @return String returns null if OK else it returns the reason why its is not removed
	 */
	public boolean confimDistrictKRngComboExists(
		String sDistrict,
		String sKieskringNum)
		throws KOAException
	{
		boolean bReturn = false;
		//We store the District in a hash map using the combo as a unique key
		//Cant us sKieskringNum on its own as it may not be unique
		String sHashKey = sDistrict + "-" + sKieskringNum;
		String sDistrictFound = (String) htDistrictKieskring.get(sHashKey);
		if (sDistrictFound == null || sDistrictFound.equals(""))
		{
			//find if the District/KR combo is in the db
			if (findComboInDB(sDistrict, sKieskringNum))
			{
				//store the valid combo in out hashtable
				htDistrictKieskring.put(sHashKey, sDistrict);
				//combo exists in the db then allow this record to be processed
				bReturn = true;
			}
			else
			{
				//combo doesnt exists in the hash table or the db
				//then dont allow this record to be processed				
				bReturn = false;
			}
		}
		else
		{
			// District/kieskring comboo is ok contiue processing the record
			bReturn = true;
		}
		return bReturn;
	}
	/**
	 * Check if the Kiesring and District combo exists in the db
	 * 
	 * @param String sDistrictNummer
	 * @param String sKieskringNummer
	 * @return String returns true if combo exists else false
	 */
	public boolean findComboInDB(
		String sDistrictNummer,
		String sKieskringNummer)
		throws KOAException
	{
		boolean bReturn = false;
		try
		{
			DistrictenHome xDistrictenHome =
				ObjectCache.getInstance().getDistrictenHome();
			try
			{
				KieskringenKey inKey = new KieskringenKey(sKieskringNummer);
				Enumeration xDistrictEnum =
					xDistrictenHome.findDistrictenByFk_dist_kkr(inKey);
				//May be more than one District returned with the KiesKringnummer
				while (xDistrictEnum.hasMoreElements())
				{
					Districten xDistrictenFromDB =
						(Districten) xDistrictEnum.nextElement();
					DistrictenKey xDistricktenKey =
						(DistrictenKey) xDistrictenFromDB.getPrimaryKey();
					if (xDistricktenKey.districtnummer.equals(sDistrictNummer))
					{
						return true;
					}
				}
				return bReturn;
			}
			catch (FinderException finderE)
			{
				// unknown keiskring
				return false;
			}
		}
		catch (RemoteException ne)
		{
			String[] params = { "Districten" };
			KOALogHelper.logErrorCode(
				"KiesRegisterAdminHelperBean",
				ErrorConstants.ERR_REMOTE,
				params,
				ne);
			throw new KOADataBeheerException(
				KOADataBeheerException.EJBEXCEPTION,
				ne);
		}
	}
}