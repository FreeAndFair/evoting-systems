package com.logicacmg.koa.kr.beans;
import com.ibm.ejs.persistence.*;
import javax.ejb.EntityBean;
import java.sql.*;
import java.text.*;
import com.ibm.vap.converters.*;
import com.ibm.vap.converters.streams.*;
/**
 * EJSJDBCPersisterCMPKiezersBean
 * @generated
 */
public class EJSJDBCPersisterCMPKiezersBean extends EJSJDBCPersister implements com.logicacmg.koa.kr.beans.EJSFinderKiezersBean {
	/**
	 * @generated
	 */
	private static final String _createString = "INSERT INTO KOA01.KIEZERS (STEMCODE, KIEZERIDENTIFICATIE, HASHEDWACHTWOORD, DISTRICTNUMMER, KIESKRINGNUMMER, REEDSGESTEMD, TIMESTAMPGESTEMD, MODALITEIT, TRANSACTIENUMMER, VALIDLOGINS, INVALIDLOGINS, LOGINATTEMPTSLEFT, TIMELASTSUCCESFULLOGIN, ACCOUNTLOCKED, TIMESTAMPUNLOCK, VERWIJDERD) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)";
	/**
	 * @generated
	 */
	private static final String _removeString = "DELETE FROM KOA01.KIEZERS  WHERE STEMCODE = ?";
	/**
	 * @generated
	 */
	private static final String _storeString = "UPDATE KOA01.KIEZERS  SET KIEZERIDENTIFICATIE = ?, HASHEDWACHTWOORD = ?, DISTRICTNUMMER = ?, KIESKRINGNUMMER = ?, REEDSGESTEMD = ?, TIMESTAMPGESTEMD = ?, MODALITEIT = ?, TRANSACTIENUMMER = ?, VALIDLOGINS = ?, INVALIDLOGINS = ?, LOGINATTEMPTSLEFT = ?, TIMELASTSUCCESFULLOGIN = ?, ACCOUNTLOCKED = ?, TIMESTAMPUNLOCK = ?, VERWIJDERD = ? WHERE STEMCODE = ?";
	/**
	 * @generated
	 */
	private static final String _loadString = "SELECT T1.STEMCODE, T1.KIEZERIDENTIFICATIE, T1.HASHEDWACHTWOORD, T1.DISTRICTNUMMER, T1.KIESKRINGNUMMER, T1.REEDSGESTEMD, T1.TIMESTAMPGESTEMD, T1.MODALITEIT, T1.TRANSACTIENUMMER, T1.VALIDLOGINS, T1.INVALIDLOGINS, T1.LOGINATTEMPTSLEFT, T1.TIMELASTSUCCESFULLOGIN, T1.ACCOUNTLOCKED, T1.TIMESTAMPUNLOCK, T1.VERWIJDERD FROM KOA01.KIEZERS  T1 WHERE T1.STEMCODE = ?";
	/**
	 * @generated
	 */
	private static final String _loadForUpdateString = _loadString + " FOR UPDATE";
	/**
	 * @generated
	 */
	private byte[] serObj = null;
	/**
	 * EJSJDBCPersisterCMPKiezersBean
	 * @generated
	 */
	public EJSJDBCPersisterCMPKiezersBean() throws java.rmi.RemoteException {
		super();	}
	/**
	 * postInit
	 * @generated
	 */
	public void postInit() {
	}
	/**
	 * _create
	 * @generated
	 */
	public void _create(EntityBean eb) throws Exception {
		Object objectTemp = null;
		KiezersBean b = (KiezersBean) eb;
		PreparedStatement pstmt;
		pstmt = getPreparedStatement(_createString);
		try {
			if (b.stemcode == null) {
				pstmt.setNull(1, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(1, b.stemcode);
			}
			if (b.kiezeridentificatie == null) {
				pstmt.setNull(2, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(2, b.kiezeridentificatie);
			}
			if (b.hashedwachtwoord == null) {
				pstmt.setNull(3, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(3, b.hashedwachtwoord);
			}
			if (b.districtnummer == null) {
				pstmt.setNull(4, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(4, b.districtnummer);
			}
			if (b.kieskringnummer == null) {
				pstmt.setNull(5, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(5, b.kieskringnummer);
			}
			objectTemp = com.ibm.vap.converters.VapCharToBoolean.singleton().dataFrom(b.reedsgestemd);
			if (objectTemp == null) {
				pstmt.setNull(6, java.sql.Types.CHAR);
			}
			else {
				pstmt.setString(6, (java.lang.String)objectTemp);
			}
			if (b.timestampgestemd == null) {
				pstmt.setNull(7, java.sql.Types.TIMESTAMP);
			}
			else {
				pstmt.setTimestamp(7, b.timestampgestemd);
			}
			if (b.modaliteit == null) {
				pstmt.setNull(8, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(8, b.modaliteit);
			}
			if (b.transactienummer == null) {
				pstmt.setNull(9, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(9, b.transactienummer);
			}
			if (b.validlogins == null) {
				pstmt.setNull(10, java.sql.Types.INTEGER);
			}
			else {
				pstmt.setInt(10, b.validlogins.intValue());
			}
			if (b.invalidlogins == null) {
				pstmt.setNull(11, java.sql.Types.INTEGER);
			}
			else {
				pstmt.setInt(11, b.invalidlogins.intValue());
			}
			if (b.loginattemptsleft == null) {
				pstmt.setNull(12, java.sql.Types.INTEGER);
			}
			else {
				pstmt.setInt(12, b.loginattemptsleft.intValue());
			}
			if (b.timelastsuccesfullogin == null) {
				pstmt.setNull(13, java.sql.Types.TIMESTAMP);
			}
			else {
				pstmt.setTimestamp(13, b.timelastsuccesfullogin);
			}
			objectTemp = com.ibm.vap.converters.VapCharToBoolean.singleton().dataFrom(b.accountlocked);
			if (objectTemp == null) {
				pstmt.setNull(14, java.sql.Types.CHAR);
			}
			else {
				pstmt.setString(14, (java.lang.String)objectTemp);
			}
			if (b.timestampunlock == null) {
				pstmt.setNull(15, java.sql.Types.TIMESTAMP);
			}
			else {
				pstmt.setTimestamp(15, b.timestampunlock);
			}
			objectTemp = com.ibm.vap.converters.VapCharToBoolean.singleton().dataFrom(b.verwijderd);
			if (objectTemp == null) {
				pstmt.setNull(16, java.sql.Types.CHAR);
			}
			else {
				pstmt.setString(16, (java.lang.String)objectTemp);
			}
			pstmt.executeUpdate();
		}
		finally {
			returnPreparedStatement(pstmt);
		}
	}
	/**
	 * hydrate
	 * @generated
	 */
	public void hydrate(EntityBean eb, Object data, Object pKey) throws Exception {
		Object objectTemp = null;
		KiezersBean b = (KiezersBean) eb;
		com.logicacmg.koa.kr.beans.KiezersKey _primaryKey = (com.logicacmg.koa.kr.beans.KiezersKey)pKey;
		java.sql.ResultSet resultSet = (java.sql.ResultSet) data;
		int intTemp;
		b.stemcode = _primaryKey.stemcode;
		b.kiezeridentificatie = resultSet.getString(2);
		b.hashedwachtwoord = resultSet.getString(3);
		b.districtnummer = resultSet.getString(4);
		b.kieskringnummer = resultSet.getString(5);
		b.reedsgestemd = (java.lang.Boolean)com.ibm.vap.converters.VapCharToBoolean.singleton().objectFrom(resultSet.getString(6));
		b.timestampgestemd = resultSet.getTimestamp(7);
		b.modaliteit = resultSet.getString(8);
		b.transactienummer = resultSet.getString(9);
		intTemp = resultSet.getInt(10);
		b.validlogins = resultSet.wasNull() ? null : new Integer(intTemp);
		intTemp = resultSet.getInt(11);
		b.invalidlogins = resultSet.wasNull() ? null : new Integer(intTemp);
		intTemp = resultSet.getInt(12);
		b.loginattemptsleft = resultSet.wasNull() ? null : new Integer(intTemp);
		b.timelastsuccesfullogin = resultSet.getTimestamp(13);
		b.accountlocked = (java.lang.Boolean)com.ibm.vap.converters.VapCharToBoolean.singleton().objectFrom(resultSet.getString(14));
		b.timestampunlock = resultSet.getTimestamp(15);
		b.verwijderd = (java.lang.Boolean)com.ibm.vap.converters.VapCharToBoolean.singleton().objectFrom(resultSet.getString(16));
	}
	/**
	 * load
	 * @generated
	 */
	public void load(EntityBean eb, Object pKey, boolean forUpdate) throws Exception {
		Object objectTemp = null;
		KiezersBean b = (KiezersBean) eb;
		com.logicacmg.koa.kr.beans.KiezersKey _primaryKey = (com.logicacmg.koa.kr.beans.KiezersKey)pKey;
		PreparedStatement pstmt;
		ResultSet resultSet = null;
		pstmt = (forUpdate) ?
			getPreparedStatement(_loadForUpdateString):
			getPreparedStatement(_loadString);
		try {
			if (_primaryKey.stemcode == null) {
				pstmt.setNull(1, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(1, _primaryKey.stemcode);
			}
			resultSet = pstmt.executeQuery();
			if (!(resultSet.next())) throw new javax.ejb.ObjectNotFoundException();
			hydrate(eb, resultSet, pKey);
		}
		finally {
			if (resultSet != null) resultSet.close();
			returnPreparedStatement(pstmt);
		}
	}
	/**
	 * refresh
	 * @generated
	 */
	public void refresh(EntityBean eb, boolean forUpdate) throws Exception {
		KiezersBean b = (KiezersBean) eb;
		com.logicacmg.koa.kr.beans.KiezersKey _primaryKey = new com.logicacmg.koa.kr.beans.KiezersKey();
		_primaryKey.stemcode = b.stemcode;
		load(b, _primaryKey, forUpdate);
	}
	/**
	 * store
	 * @generated
	 */
	public void store(EntityBean eb) throws Exception {
		Object objectTemp = null;
		KiezersBean b = (KiezersBean) eb;
		com.logicacmg.koa.kr.beans.KiezersKey _primaryKey = new com.logicacmg.koa.kr.beans.KiezersKey();
		_primaryKey.stemcode = b.stemcode;
		PreparedStatement pstmt;
		pstmt = getPreparedStatement(_storeString);
		try {
			if (_primaryKey.stemcode == null) {
				pstmt.setNull(16, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(16, _primaryKey.stemcode);
			}
			if (b.kiezeridentificatie == null) {
				pstmt.setNull(1, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(1, b.kiezeridentificatie);
			}
			if (b.hashedwachtwoord == null) {
				pstmt.setNull(2, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(2, b.hashedwachtwoord);
			}
			if (b.districtnummer == null) {
				pstmt.setNull(3, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(3, b.districtnummer);
			}
			if (b.kieskringnummer == null) {
				pstmt.setNull(4, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(4, b.kieskringnummer);
			}
			objectTemp = com.ibm.vap.converters.VapCharToBoolean.singleton().dataFrom(b.reedsgestemd);
			if (objectTemp == null) {
				pstmt.setNull(5, java.sql.Types.CHAR);
			}
			else {
				pstmt.setString(5, (java.lang.String)objectTemp);
			}
			if (b.timestampgestemd == null) {
				pstmt.setNull(6, java.sql.Types.TIMESTAMP);
			}
			else {
				pstmt.setTimestamp(6, b.timestampgestemd);
			}
			if (b.modaliteit == null) {
				pstmt.setNull(7, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(7, b.modaliteit);
			}
			if (b.transactienummer == null) {
				pstmt.setNull(8, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(8, b.transactienummer);
			}
			if (b.validlogins == null) {
				pstmt.setNull(9, java.sql.Types.INTEGER);
			}
			else {
				pstmt.setInt(9, b.validlogins.intValue());
			}
			if (b.invalidlogins == null) {
				pstmt.setNull(10, java.sql.Types.INTEGER);
			}
			else {
				pstmt.setInt(10, b.invalidlogins.intValue());
			}
			if (b.loginattemptsleft == null) {
				pstmt.setNull(11, java.sql.Types.INTEGER);
			}
			else {
				pstmt.setInt(11, b.loginattemptsleft.intValue());
			}
			if (b.timelastsuccesfullogin == null) {
				pstmt.setNull(12, java.sql.Types.TIMESTAMP);
			}
			else {
				pstmt.setTimestamp(12, b.timelastsuccesfullogin);
			}
			objectTemp = com.ibm.vap.converters.VapCharToBoolean.singleton().dataFrom(b.accountlocked);
			if (objectTemp == null) {
				pstmt.setNull(13, java.sql.Types.CHAR);
			}
			else {
				pstmt.setString(13, (java.lang.String)objectTemp);
			}
			if (b.timestampunlock == null) {
				pstmt.setNull(14, java.sql.Types.TIMESTAMP);
			}
			else {
				pstmt.setTimestamp(14, b.timestampunlock);
			}
			objectTemp = com.ibm.vap.converters.VapCharToBoolean.singleton().dataFrom(b.verwijderd);
			if (objectTemp == null) {
				pstmt.setNull(15, java.sql.Types.CHAR);
			}
			else {
				pstmt.setString(15, (java.lang.String)objectTemp);
			}
			pstmt.executeUpdate();
		}
		finally {
			returnPreparedStatement(pstmt);
		}
	}
	/**
	 * remove
	 * @generated
	 */
	public void remove(EntityBean eb) throws Exception {
		Object objectTemp = null;
		KiezersBean b = (KiezersBean) eb;
		com.logicacmg.koa.kr.beans.KiezersKey _primaryKey = new com.logicacmg.koa.kr.beans.KiezersKey();
		_primaryKey.stemcode = b.stemcode;
		PreparedStatement pstmt;
		pstmt = getPreparedStatement(_removeString);
		try {
			if (_primaryKey.stemcode == null) {
				pstmt.setNull(1, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(1, _primaryKey.stemcode);
			}
			pstmt.executeUpdate();
		}
		finally {
			returnPreparedStatement(pstmt);
		}
	}
	/**
	 * getPrimaryKey
	 * @generated
	 */
	public Object getPrimaryKey(Object data) throws Exception {
		com.logicacmg.koa.kr.beans.KiezersKey key = new com.logicacmg.koa.kr.beans.KiezersKey();
		java.sql.ResultSet resultSet = (java.sql.ResultSet) data;

		if (resultSet != null) {
			Object objectTemp = null;
			key.stemcode = resultSet.getString(1);
			return key;
		}
		return null;
	}
	/**
	 * findByPrimaryKey
	 * @generated
	 */
	public com.logicacmg.koa.kr.beans.Kiezers findByPrimaryKey(com.logicacmg.koa.kr.beans.KiezersKey primaryKey) throws java.rmi.RemoteException, javax.ejb.FinderException {
		return (com.logicacmg.koa.kr.beans.Kiezers) home.activateBean(primaryKey);
	}
	/**
	 * findByKiezerId
	 * @generated
	 */
	public com.logicacmg.koa.kr.beans.Kiezers findByKiezerId(java.lang.String sKiezerId) throws javax.ejb.FinderException, java.rmi.RemoteException {
		ResultSet resultSet = null;
		PreparedStatement pstmt = null;
		com.logicacmg.koa.kr.beans.Kiezers result = null;

		EJSJDBCFinder tmpFinder = null;
		try {
			preFind();
			pstmt = getPreparedStatement("SELECT T1.STEMCODE, T1.KIEZERIDENTIFICATIE, T1.HASHEDWACHTWOORD, T1.DISTRICTNUMMER, T1.KIESKRINGNUMMER, T1.REEDSGESTEMD, T1.TIMESTAMPGESTEMD, T1.MODALITEIT, T1.TRANSACTIENUMMER, T1.VALIDLOGINS, T1.INVALIDLOGINS, T1.LOGINATTEMPTSLEFT, T1.TIMELASTSUCCESFULLOGIN, T1.ACCOUNTLOCKED, T1.TIMESTAMPUNLOCK, T1.VERWIJDERD FROM KOA01.KIEZERS  T1 WHERE kiezeridentificatie = ?");
			if (sKiezerId == null) {
			   pstmt.setNull(1, java.sql.Types.VARCHAR);
			} else {
			   pstmt.setString(1, sKiezerId);
			}
			resultSet = pstmt.executeQuery();
			tmpFinder = new EJSJDBCFinder(resultSet, this, pstmt);
			if (tmpFinder.hasMoreElements()) {
				result = (com.logicacmg.koa.kr.beans.Kiezers)tmpFinder.nextElement();
			}
		}
		catch (Exception ex) {
			throw new EJSPersistenceException("find failed:", ex);
		}
		finally {
			if ( tmpFinder != null ) tmpFinder.close();
		}
		if (result == null) {
			throw new javax.ejb.ObjectNotFoundException();
		}
		return result;
	}
}
