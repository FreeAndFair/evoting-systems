package com.logicacmg.koa.sar;
import com.ibm.ejs.persistence.*;
import javax.ejb.EntityBean;
import java.sql.*;
import java.text.*;
import com.ibm.vap.converters.*;
import com.ibm.vap.converters.streams.*;
/**
 * EJSJDBCPersisterCMPSarBean
 * @generated
 */
public class EJSJDBCPersisterCMPSarBean extends EJSJDBCPersister implements com.logicacmg.koa.sar.EJSFinderSarBean {
	/**
	 * @generated
	 */
	private static final String _createString = "INSERT INTO KOA01.SAR (KIEZERIDENTIFICATIE, STEMCODE) VALUES (?, ?)";
	/**
	 * @generated
	 */
	private static final String _removeString = "DELETE FROM KOA01.SAR  WHERE KIEZERIDENTIFICATIE = ?";
	/**
	 * @generated
	 */
	private static final String _storeString = "UPDATE KOA01.SAR  SET STEMCODE = ? WHERE KIEZERIDENTIFICATIE = ?";
	/**
	 * @generated
	 */
	private static final String _loadString = "SELECT T1.KIEZERIDENTIFICATIE, T1.STEMCODE FROM KOA01.SAR  T1 WHERE T1.KIEZERIDENTIFICATIE = ?";
	/**
	 * @generated
	 */
	private static final String _loadForUpdateString = _loadString + " FOR UPDATE";
	/**
	 * @generated
	 */
	private byte[] serObj = null;
	/**
	 * EJSJDBCPersisterCMPSarBean
	 * @generated
	 */
	public EJSJDBCPersisterCMPSarBean() throws java.rmi.RemoteException {
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
		SarBean b = (SarBean) eb;
		PreparedStatement pstmt;
		pstmt = getPreparedStatement(_createString);
		try {
			if (b.kiezeridentificatie == null) {
				pstmt.setNull(1, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(1, b.kiezeridentificatie);
			}
			if (b.stemcode == null) {
				pstmt.setNull(2, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(2, b.stemcode);
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
		SarBean b = (SarBean) eb;
		com.logicacmg.koa.sar.SarKey _primaryKey = (com.logicacmg.koa.sar.SarKey)pKey;
		java.sql.ResultSet resultSet = (java.sql.ResultSet) data;
		b.kiezeridentificatie = _primaryKey.kiezeridentificatie;
		b.stemcode = resultSet.getString(2);
	}
	/**
	 * load
	 * @generated
	 */
	public void load(EntityBean eb, Object pKey, boolean forUpdate) throws Exception {
		Object objectTemp = null;
		SarBean b = (SarBean) eb;
		com.logicacmg.koa.sar.SarKey _primaryKey = (com.logicacmg.koa.sar.SarKey)pKey;
		PreparedStatement pstmt;
		ResultSet resultSet = null;
		pstmt = (forUpdate) ?
			getPreparedStatement(_loadForUpdateString):
			getPreparedStatement(_loadString);
		try {
			if (_primaryKey.kiezeridentificatie == null) {
				pstmt.setNull(1, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(1, _primaryKey.kiezeridentificatie);
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
		SarBean b = (SarBean) eb;
		com.logicacmg.koa.sar.SarKey _primaryKey = new com.logicacmg.koa.sar.SarKey();
		_primaryKey.kiezeridentificatie = b.kiezeridentificatie;
		load(b, _primaryKey, forUpdate);
	}
	/**
	 * store
	 * @generated
	 */
	public void store(EntityBean eb) throws Exception {
		Object objectTemp = null;
		SarBean b = (SarBean) eb;
		com.logicacmg.koa.sar.SarKey _primaryKey = new com.logicacmg.koa.sar.SarKey();
		_primaryKey.kiezeridentificatie = b.kiezeridentificatie;
		PreparedStatement pstmt;
		pstmt = getPreparedStatement(_storeString);
		try {
			if (_primaryKey.kiezeridentificatie == null) {
				pstmt.setNull(2, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(2, _primaryKey.kiezeridentificatie);
			}
			if (b.stemcode == null) {
				pstmt.setNull(1, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(1, b.stemcode);
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
		SarBean b = (SarBean) eb;
		com.logicacmg.koa.sar.SarKey _primaryKey = new com.logicacmg.koa.sar.SarKey();
		_primaryKey.kiezeridentificatie = b.kiezeridentificatie;
		PreparedStatement pstmt;
		pstmt = getPreparedStatement(_removeString);
		try {
			if (_primaryKey.kiezeridentificatie == null) {
				pstmt.setNull(1, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(1, _primaryKey.kiezeridentificatie);
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
		com.logicacmg.koa.sar.SarKey key = new com.logicacmg.koa.sar.SarKey();
		java.sql.ResultSet resultSet = (java.sql.ResultSet) data;

		if (resultSet != null) {
			Object objectTemp = null;
			key.kiezeridentificatie = resultSet.getString(1);
			return key;
		}
		return null;
	}
	/**
	 * findByPrimaryKey
	 * @generated
	 */
	public com.logicacmg.koa.sar.Sar findByPrimaryKey(com.logicacmg.koa.sar.SarKey primaryKey) throws java.rmi.RemoteException, javax.ejb.FinderException {
		return (com.logicacmg.koa.sar.Sar) home.activateBean(primaryKey);
	}
	/**
	 * findByStemcode
	 * @generated
	 */
	public com.logicacmg.koa.sar.Sar findByStemcode(java.lang.String sStemcode) throws javax.ejb.FinderException, java.rmi.RemoteException {
		ResultSet resultSet = null;
		PreparedStatement pstmt = null;
		com.logicacmg.koa.sar.Sar result = null;

		EJSJDBCFinder tmpFinder = null;
		try {
			preFind();
			pstmt = getPreparedStatement("SELECT T1.KIEZERIDENTIFICATIE, T1.STEMCODE FROM KOA01.SAR  T1 WHERE stemcode = ?");
			if (sStemcode == null) {
			   pstmt.setNull(1, java.sql.Types.VARCHAR);
			} else {
			   pstmt.setString(1, sStemcode);
			}
			resultSet = pstmt.executeQuery();
			tmpFinder = new EJSJDBCFinder(resultSet, this, pstmt);
			if (tmpFinder.hasMoreElements()) {
				result = (com.logicacmg.koa.sar.Sar)tmpFinder.nextElement();
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
