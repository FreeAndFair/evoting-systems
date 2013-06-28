package com.logicacmg.koa.esb.beans;
import com.ibm.ejs.persistence.*;
import javax.ejb.EntityBean;
import java.sql.*;
import java.text.*;
import com.ibm.vap.converters.*;
import com.ibm.vap.converters.streams.*;
/**
 * EJSJDBCPersisterCMPEsbfingerprintsBean
 * @generated
 */
public class EJSJDBCPersisterCMPEsbfingerprintsBean extends EJSJDBCPersister implements com.logicacmg.koa.esb.beans.EJSFinderEsbfingerprintsBean {
	/**
	 * @generated
	 */
	private static final String _createString = "INSERT INTO KOA01.ESBFINGERPRINTS (ID, FINGERPRINT, TIMESTAMP, SYSTEMSTATUS) VALUES (?, ?, ?, ?)";
	/**
	 * @generated
	 */
	private static final String _removeString = "DELETE FROM KOA01.ESBFINGERPRINTS  WHERE ID = ?";
	/**
	 * @generated
	 */
	private static final String _storeString = "UPDATE KOA01.ESBFINGERPRINTS  SET FINGERPRINT = ?, TIMESTAMP = ?, SYSTEMSTATUS = ? WHERE ID = ?";
	/**
	 * @generated
	 */
	private static final String _loadString = "SELECT T1.ID, T1.FINGERPRINT, T1.TIMESTAMP, T1.SYSTEMSTATUS FROM KOA01.ESBFINGERPRINTS  T1 WHERE T1.ID = ?";
	/**
	 * @generated
	 */
	private static final String _loadForUpdateString = _loadString + " FOR UPDATE";
	/**
	 * @generated
	 */
	private byte[] serObj = null;
	/**
	 * EJSJDBCPersisterCMPEsbfingerprintsBean
	 * @generated
	 */
	public EJSJDBCPersisterCMPEsbfingerprintsBean() throws java.rmi.RemoteException {
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
		EsbfingerprintsBean b = (EsbfingerprintsBean) eb;
		PreparedStatement pstmt;
		pstmt = getPreparedStatement(_createString);
		try {
			if (b.id == null) {
				pstmt.setNull(1, java.sql.Types.DECIMAL);
			}
			else {
				pstmt.setBigDecimal(1, b.id);
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
	 * hydrate
	 * @generated
	 */
	public void hydrate(EntityBean eb, Object data, Object pKey) throws Exception {
		Object objectTemp = null;
		EsbfingerprintsBean b = (EsbfingerprintsBean) eb;
		com.logicacmg.koa.esb.beans.EsbfingerprintsKey _primaryKey = (com.logicacmg.koa.esb.beans.EsbfingerprintsKey)pKey;
		java.sql.ResultSet resultSet = (java.sql.ResultSet) data;
		b.id = _primaryKey.id;
		b.fingerprint = (byte[])com.ibm.vap.converters.streams.VapBinaryStreamToSerializableObjectConverter.singleton().objectFrom(resultSet.getBlob(2));
		b.timestamp = resultSet.getTimestamp(3);
		b.systemstatus = resultSet.getString(4);
	}
	/**
	 * load
	 * @generated
	 */
	public void load(EntityBean eb, Object pKey, boolean forUpdate) throws Exception {
		Object objectTemp = null;
		EsbfingerprintsBean b = (EsbfingerprintsBean) eb;
		com.logicacmg.koa.esb.beans.EsbfingerprintsKey _primaryKey = (com.logicacmg.koa.esb.beans.EsbfingerprintsKey)pKey;
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
		EsbfingerprintsBean b = (EsbfingerprintsBean) eb;
		com.logicacmg.koa.esb.beans.EsbfingerprintsKey _primaryKey = new com.logicacmg.koa.esb.beans.EsbfingerprintsKey();
		_primaryKey.id = b.id;
		load(b, _primaryKey, forUpdate);
	}
	/**
	 * store
	 * @generated
	 */
	public void store(EntityBean eb) throws Exception {
		Object objectTemp = null;
		EsbfingerprintsBean b = (EsbfingerprintsBean) eb;
		com.logicacmg.koa.esb.beans.EsbfingerprintsKey _primaryKey = new com.logicacmg.koa.esb.beans.EsbfingerprintsKey();
		_primaryKey.id = b.id;
		PreparedStatement pstmt;
		pstmt = getPreparedStatement(_storeString);
		try {
			if (_primaryKey.id == null) {
				pstmt.setNull(4, java.sql.Types.DECIMAL);
			}
			else {
				pstmt.setBigDecimal(4, _primaryKey.id);
			}
			objectTemp = com.ibm.vap.converters.streams.VapBinaryStreamToSerializableObjectConverter.singleton().dataFrom(b.fingerprint);
			if (objectTemp == null) {
				pstmt.setNull(1, java.sql.Types.BLOB);
			}
			else {
				pstmt.setBinaryStream(1, new java.io.ByteArrayInputStream((byte[])objectTemp), ((byte[])objectTemp).length);
			}
			if (b.timestamp == null) {
				pstmt.setNull(2, java.sql.Types.TIMESTAMP);
			}
			else {
				pstmt.setTimestamp(2, b.timestamp);
			}
			if (b.systemstatus == null) {
				pstmt.setNull(3, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(3, b.systemstatus);
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
		EsbfingerprintsBean b = (EsbfingerprintsBean) eb;
		com.logicacmg.koa.esb.beans.EsbfingerprintsKey _primaryKey = new com.logicacmg.koa.esb.beans.EsbfingerprintsKey();
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
		com.logicacmg.koa.esb.beans.EsbfingerprintsKey key = new com.logicacmg.koa.esb.beans.EsbfingerprintsKey();
		java.sql.ResultSet resultSet = (java.sql.ResultSet) data;

		if (resultSet != null) {
			Object objectTemp = null;
			key.id = resultSet.getBigDecimal(1);
			return key;
		}
		return null;
	}
	/**
	 * findByPrimaryKey
	 * @generated
	 */
	public com.logicacmg.koa.esb.beans.Esbfingerprints findByPrimaryKey(com.logicacmg.koa.esb.beans.EsbfingerprintsKey primaryKey) throws java.rmi.RemoteException, javax.ejb.FinderException {
		return (com.logicacmg.koa.esb.beans.Esbfingerprints) home.activateBean(primaryKey);
	}
	/**
	 * findLatestFingerprint
	 * @generated
	 */
	public com.logicacmg.koa.esb.beans.Esbfingerprints findLatestFingerprint() throws javax.ejb.FinderException, java.rmi.RemoteException {
		ResultSet resultSet = null;
		PreparedStatement pstmt = null;
		com.logicacmg.koa.esb.beans.Esbfingerprints result = null;

		EJSJDBCFinder tmpFinder = null;
		try {
			preFind();
			pstmt = getPreparedStatement("SELECT T1.ID, T1.FINGERPRINT, T1.TIMESTAMP, T1.SYSTEMSTATUS FROM KOA01.ESBFINGERPRINTS  T1 WHERE 1=1 order by id desc fetch first 1 rows only");
			resultSet = pstmt.executeQuery();
			tmpFinder = new EJSJDBCFinder(resultSet, this, pstmt);
			if (tmpFinder.hasMoreElements()) {
				result = (com.logicacmg.koa.esb.beans.Esbfingerprints)tmpFinder.nextElement();
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
