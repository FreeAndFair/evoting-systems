package com.logicacmg.koa.kr.beans;
import com.ibm.ejs.persistence.*;
import javax.ejb.EntityBean;
import java.sql.*;
import java.text.*;
import com.ibm.vap.converters.*;
import com.ibm.vap.converters.streams.*;
/**
 * EJSJDBCPersisterCMPKRFingerprintsBean
 * @generated
 */
public class EJSJDBCPersisterCMPKRFingerprintsBean extends EJSJDBCPersister implements com.logicacmg.koa.kr.beans.EJSFinderKRFingerprintsBean {
	/**
	 * @generated
	 */
	private static final String _createString = "INSERT INTO KOA01.KRFINGERPRINTS (ID, TYPE, FINGERPRINT, TIMESTAMP, SYSTEMSTATUS) VALUES (?, ?, ?, ?, ?)";
	/**
	 * @generated
	 */
	private static final String _removeString = "DELETE FROM KOA01.KRFINGERPRINTS  WHERE ID = ?";
	/**
	 * @generated
	 */
	private static final String _storeString = "UPDATE KOA01.KRFINGERPRINTS  SET TYPE = ?, FINGERPRINT = ?, TIMESTAMP = ?, SYSTEMSTATUS = ? WHERE ID = ?";
	/**
	 * @generated
	 */
	private static final String _loadString = "SELECT T1.ID, T1.TYPE, T1.FINGERPRINT, T1.TIMESTAMP, T1.SYSTEMSTATUS FROM KOA01.KRFINGERPRINTS  T1 WHERE T1.ID = ?";
	/**
	 * @generated
	 */
	private static final String _loadForUpdateString = _loadString + " FOR UPDATE";
	/**
	 * @generated
	 */
	private byte[] serObj = null;
	/**
	 * EJSJDBCPersisterCMPKRFingerprintsBean
	 * @generated
	 */
	public EJSJDBCPersisterCMPKRFingerprintsBean() throws java.rmi.RemoteException {
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
		KRFingerprintsBean b = (KRFingerprintsBean) eb;
		PreparedStatement pstmt;
		pstmt = getPreparedStatement(_createString);
		try {
			if (b.id == null) {
				pstmt.setNull(1, java.sql.Types.DECIMAL);
			}
			else {
				pstmt.setBigDecimal(1, b.id);
			}
			if (b.type == null) {
				pstmt.setNull(2, java.sql.Types.SMALLINT);
			}
			else {
				pstmt.setShort(2, b.type.shortValue());
			}
			objectTemp = com.ibm.vap.converters.streams.VapBinaryStreamToSerializableObjectConverter.singleton().dataFrom(b.fingerprint);
			if (objectTemp == null) {
				pstmt.setNull(3, java.sql.Types.BLOB);
			}
			else {
				pstmt.setBinaryStream(3, new java.io.ByteArrayInputStream((byte[])objectTemp), ((byte[])objectTemp).length);
			}
			if (b.timestamp == null) {
				pstmt.setNull(4, java.sql.Types.TIMESTAMP);
			}
			else {
				pstmt.setTimestamp(4, b.timestamp);
			}
			if (b.systemstatus == null) {
				pstmt.setNull(5, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(5, b.systemstatus);
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
		KRFingerprintsBean b = (KRFingerprintsBean) eb;
		com.logicacmg.koa.kr.beans.KRFingerprintsKey _primaryKey = (com.logicacmg.koa.kr.beans.KRFingerprintsKey)pKey;
		java.sql.ResultSet resultSet = (java.sql.ResultSet) data;
		short shortTemp;
		b.id = _primaryKey.id;
		shortTemp = resultSet.getShort(2);
		b.type = resultSet.wasNull() ? null : new Short(shortTemp);
		b.fingerprint = (byte[])com.ibm.vap.converters.streams.VapBinaryStreamToSerializableObjectConverter.singleton().objectFrom(resultSet.getBlob(3));
		b.timestamp = resultSet.getTimestamp(4);
		b.systemstatus = resultSet.getString(5);
	}
	/**
	 * load
	 * @generated
	 */
	public void load(EntityBean eb, Object pKey, boolean forUpdate) throws Exception {
		Object objectTemp = null;
		KRFingerprintsBean b = (KRFingerprintsBean) eb;
		com.logicacmg.koa.kr.beans.KRFingerprintsKey _primaryKey = (com.logicacmg.koa.kr.beans.KRFingerprintsKey)pKey;
		PreparedStatement pstmt;
		ResultSet resultSet = null;
		pstmt = (forUpdate) ?
			getPreparedStatement(_loadForUpdateString):
			getPreparedStatement(_loadString);
		try {
			if (_primaryKey.id == null) {
				pstmt.setNull(1, java.sql.Types.DECIMAL);
			}
			else {
				pstmt.setBigDecimal(1, _primaryKey.id);
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
		KRFingerprintsBean b = (KRFingerprintsBean) eb;
		com.logicacmg.koa.kr.beans.KRFingerprintsKey _primaryKey = new com.logicacmg.koa.kr.beans.KRFingerprintsKey();
		_primaryKey.id = b.id;
		load(b, _primaryKey, forUpdate);
	}
	/**
	 * store
	 * @generated
	 */
	public void store(EntityBean eb) throws Exception {
		Object objectTemp = null;
		KRFingerprintsBean b = (KRFingerprintsBean) eb;
		com.logicacmg.koa.kr.beans.KRFingerprintsKey _primaryKey = new com.logicacmg.koa.kr.beans.KRFingerprintsKey();
		_primaryKey.id = b.id;
		PreparedStatement pstmt;
		pstmt = getPreparedStatement(_storeString);
		try {
			if (_primaryKey.id == null) {
				pstmt.setNull(5, java.sql.Types.DECIMAL);
			}
			else {
				pstmt.setBigDecimal(5, _primaryKey.id);
			}
			if (b.type == null) {
				pstmt.setNull(1, java.sql.Types.SMALLINT);
			}
			else {
				pstmt.setShort(1, b.type.shortValue());
			}
			objectTemp = com.ibm.vap.converters.streams.VapBinaryStreamToSerializableObjectConverter.singleton().dataFrom(b.fingerprint);
			if (objectTemp == null) {
				pstmt.setNull(2, java.sql.Types.BLOB);
			}
			else {
				pstmt.setBinaryStream(2, new java.io.ByteArrayInputStream((byte[])objectTemp), ((byte[])objectTemp).length);
			}
			if (b.timestamp == null) {
				pstmt.setNull(3, java.sql.Types.TIMESTAMP);
			}
			else {
				pstmt.setTimestamp(3, b.timestamp);
			}
			if (b.systemstatus == null) {
				pstmt.setNull(4, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(4, b.systemstatus);
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
		KRFingerprintsBean b = (KRFingerprintsBean) eb;
		com.logicacmg.koa.kr.beans.KRFingerprintsKey _primaryKey = new com.logicacmg.koa.kr.beans.KRFingerprintsKey();
		_primaryKey.id = b.id;
		PreparedStatement pstmt;
		pstmt = getPreparedStatement(_removeString);
		try {
			if (_primaryKey.id == null) {
				pstmt.setNull(1, java.sql.Types.DECIMAL);
			}
			else {
				pstmt.setBigDecimal(1, _primaryKey.id);
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
		com.logicacmg.koa.kr.beans.KRFingerprintsKey key = new com.logicacmg.koa.kr.beans.KRFingerprintsKey();
		java.sql.ResultSet resultSet = (java.sql.ResultSet) data;

		if (resultSet != null) {
			Object objectTemp = null;
			key.id = resultSet.getBigDecimal(1);
			return key;
		}
		return null;
	}
	/**
	 * findLatestFingerprint
	 * @generated
	 */
	public com.logicacmg.koa.kr.beans.KRFingerprints findLatestFingerprint(java.lang.Integer type) throws javax.ejb.FinderException, java.rmi.RemoteException {
		ResultSet resultSet = null;
		PreparedStatement pstmt = null;
		com.logicacmg.koa.kr.beans.KRFingerprints result = null;

		EJSJDBCFinder tmpFinder = null;
		try {
			preFind();
			pstmt = getPreparedStatement("SELECT T1.ID, T1.TYPE, T1.FINGERPRINT, T1.TIMESTAMP, T1.SYSTEMSTATUS FROM KOA01.KRFINGERPRINTS  T1 WHERE type=? order by id desc fetch first 1 rows only");
			pstmt.setObject(1, type);
			resultSet = pstmt.executeQuery();
			tmpFinder = new EJSJDBCFinder(resultSet, this, pstmt);
			if (tmpFinder.hasMoreElements()) {
				result = (com.logicacmg.koa.kr.beans.KRFingerprints)tmpFinder.nextElement();
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
	/**
	 * findLastDynamicFP
	 * @generated
	 */
	public com.logicacmg.koa.kr.beans.KRFingerprints findLastDynamicFP(java.lang.Integer type, java.lang.String firstState, java.lang.String secondState) throws javax.ejb.FinderException, java.rmi.RemoteException {
		ResultSet resultSet = null;
		PreparedStatement pstmt = null;
		com.logicacmg.koa.kr.beans.KRFingerprints result = null;

		EJSJDBCFinder tmpFinder = null;
		try {
			preFind();
			pstmt = getPreparedStatement("SELECT T1.ID, T1.TYPE, T1.FINGERPRINT, T1.TIMESTAMP, T1.SYSTEMSTATUS FROM KOA01.KRFINGERPRINTS  T1 WHERE type=? and (systemstatus=? or systemstatus=?) order by id desc fetch first 1 rows only");
			pstmt.setObject(1, type);
			if (firstState == null) {
			   pstmt.setNull(2, java.sql.Types.VARCHAR);
			} else {
			   pstmt.setString(2, firstState);
			}
			if (secondState == null) {
			   pstmt.setNull(3, java.sql.Types.VARCHAR);
			} else {
			   pstmt.setString(3, secondState);
			}
			resultSet = pstmt.executeQuery();
			tmpFinder = new EJSJDBCFinder(resultSet, this, pstmt);
			if (tmpFinder.hasMoreElements()) {
				result = (com.logicacmg.koa.kr.beans.KRFingerprints)tmpFinder.nextElement();
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
	/**
	 * findByPrimaryKey
	 * @generated
	 */
	public com.logicacmg.koa.kr.beans.KRFingerprints findByPrimaryKey(com.logicacmg.koa.kr.beans.KRFingerprintsKey primaryKey) throws java.rmi.RemoteException, javax.ejb.FinderException {
		return (com.logicacmg.koa.kr.beans.KRFingerprints) home.activateBean(primaryKey);
	}
	/**
	 * findByTypeAndState
	 * @generated
	 */
	public com.logicacmg.koa.kr.beans.KRFingerprints findByTypeAndState(java.lang.Integer type, java.lang.String systemstatus) throws javax.ejb.FinderException, java.rmi.RemoteException {
		ResultSet resultSet = null;
		PreparedStatement pstmt = null;
		com.logicacmg.koa.kr.beans.KRFingerprints result = null;

		EJSJDBCFinder tmpFinder = null;
		try {
			preFind();
			pstmt = getPreparedStatement("SELECT T1.ID, T1.TYPE, T1.FINGERPRINT, T1.TIMESTAMP, T1.SYSTEMSTATUS FROM KOA01.KRFINGERPRINTS  T1 WHERE type=? AND systemstatus=? order by id desc fetch first 1 rows only");
			pstmt.setObject(1, type);
			if (systemstatus == null) {
			   pstmt.setNull(2, java.sql.Types.VARCHAR);
			} else {
			   pstmt.setString(2, systemstatus);
			}
			resultSet = pstmt.executeQuery();
			tmpFinder = new EJSJDBCFinder(resultSet, this, pstmt);
			if (tmpFinder.hasMoreElements()) {
				result = (com.logicacmg.koa.kr.beans.KRFingerprints)tmpFinder.nextElement();
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
	/**
	 * findLastFP
	 * @generated
	 */
	public com.logicacmg.koa.kr.beans.KRFingerprints findLastFP() throws javax.ejb.FinderException, java.rmi.RemoteException {
		ResultSet resultSet = null;
		PreparedStatement pstmt = null;
		com.logicacmg.koa.kr.beans.KRFingerprints result = null;

		EJSJDBCFinder tmpFinder = null;
		try {
			preFind();
			pstmt = getPreparedStatement("SELECT T1.ID, T1.TYPE, T1.FINGERPRINT, T1.TIMESTAMP, T1.SYSTEMSTATUS FROM KOA01.KRFINGERPRINTS  T1 WHERE type=1 order by id desc fetch first 1 rows only");
			resultSet = pstmt.executeQuery();
			tmpFinder = new EJSJDBCFinder(resultSet, this, pstmt);
			if (tmpFinder.hasMoreElements()) {
				result = (com.logicacmg.koa.kr.beans.KRFingerprints)tmpFinder.nextElement();
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
