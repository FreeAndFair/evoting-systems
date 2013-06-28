package com.logicacmg.koa.esb.beans;
import com.ibm.ejs.persistence.*;
import javax.ejb.EntityBean;
import java.sql.*;
import java.text.*;
import com.ibm.vap.converters.*;
import com.ibm.vap.converters.streams.*;
/**
 * EJSJDBCPersisterCMPEncryptedesbBean
 * @generated
 */
public class EJSJDBCPersisterCMPEncryptedesbBean extends EJSJDBCPersister implements com.logicacmg.koa.esb.beans.EJSFinderEncryptedesbBean {
	/**
	 * @generated
	 */
	private static final String _createString = "INSERT INTO KOA01.ENCRYPTEDESB (STEMNUMMER, STEM) VALUES (?, ?)";
	/**
	 * @generated
	 */
	private static final String _removeString = "DELETE FROM KOA01.ENCRYPTEDESB  WHERE STEMNUMMER = ?";
	/**
	 * @generated
	 */
	private static final String _storeString = "UPDATE KOA01.ENCRYPTEDESB  SET STEM = ? WHERE STEMNUMMER = ?";
	/**
	 * @generated
	 */
	private static final String _loadString = "SELECT T1.STEMNUMMER, T1.STEM FROM KOA01.ENCRYPTEDESB  T1 WHERE T1.STEMNUMMER = ?";
	/**
	 * @generated
	 */
	private static final String _loadForUpdateString = _loadString + " FOR UPDATE";
	/**
	 * @generated
	 */
	private byte[] serObj = null;
	/**
	 * EJSJDBCPersisterCMPEncryptedesbBean
	 * @generated
	 */
	public EJSJDBCPersisterCMPEncryptedesbBean() throws java.rmi.RemoteException {
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
		EncryptedesbBean b = (EncryptedesbBean) eb;
		PreparedStatement pstmt;
		pstmt = getPreparedStatement(_createString);
		try {
			if (b.stemnummer == null) {
				pstmt.setNull(1, java.sql.Types.DECIMAL);
			}
			else {
				pstmt.setBigDecimal(1, b.stemnummer);
			}
			objectTemp = com.ibm.vap.converters.streams.VapBinaryStreamToByteArrayConverter.singleton().dataFrom(b.stem);
			if (objectTemp == null) {
				pstmt.setNull(2, java.sql.Types.BLOB);
			}
			else {
				pstmt.setBinaryStream(2, new java.io.ByteArrayInputStream((byte[])objectTemp), ((byte[])objectTemp).length);
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
		EncryptedesbBean b = (EncryptedesbBean) eb;
		com.logicacmg.koa.esb.beans.EncryptedesbKey _primaryKey = (com.logicacmg.koa.esb.beans.EncryptedesbKey)pKey;
		java.sql.ResultSet resultSet = (java.sql.ResultSet) data;
		b.stemnummer = _primaryKey.stemnummer;
		b.stem = (byte[])com.ibm.vap.converters.streams.VapBinaryStreamToByteArrayConverter.singleton().objectFrom(resultSet.getBlob(2));
	}
	/**
	 * load
	 * @generated
	 */
	public void load(EntityBean eb, Object pKey, boolean forUpdate) throws Exception {
		Object objectTemp = null;
		EncryptedesbBean b = (EncryptedesbBean) eb;
		com.logicacmg.koa.esb.beans.EncryptedesbKey _primaryKey = (com.logicacmg.koa.esb.beans.EncryptedesbKey)pKey;
		PreparedStatement pstmt;
		ResultSet resultSet = null;
		pstmt = (forUpdate) ?
			getPreparedStatement(_loadForUpdateString):
			getPreparedStatement(_loadString);
		try {
			if (_primaryKey.stemnummer == null) {
				pstmt.setNull(1, java.sql.Types.DECIMAL);
			}
			else {
				pstmt.setBigDecimal(1, _primaryKey.stemnummer);
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
		EncryptedesbBean b = (EncryptedesbBean) eb;
		com.logicacmg.koa.esb.beans.EncryptedesbKey _primaryKey = new com.logicacmg.koa.esb.beans.EncryptedesbKey();
		_primaryKey.stemnummer = b.stemnummer;
		load(b, _primaryKey, forUpdate);
	}
	/**
	 * store
	 * @generated
	 */
	public void store(EntityBean eb) throws Exception {
		Object objectTemp = null;
		EncryptedesbBean b = (EncryptedesbBean) eb;
		com.logicacmg.koa.esb.beans.EncryptedesbKey _primaryKey = new com.logicacmg.koa.esb.beans.EncryptedesbKey();
		_primaryKey.stemnummer = b.stemnummer;
		PreparedStatement pstmt;
		pstmt = getPreparedStatement(_storeString);
		try {
			if (_primaryKey.stemnummer == null) {
				pstmt.setNull(2, java.sql.Types.DECIMAL);
			}
			else {
				pstmt.setBigDecimal(2, _primaryKey.stemnummer);
			}
			objectTemp = com.ibm.vap.converters.streams.VapBinaryStreamToByteArrayConverter.singleton().dataFrom(b.stem);
			if (objectTemp == null) {
				pstmt.setNull(1, java.sql.Types.BLOB);
			}
			else {
				pstmt.setBinaryStream(1, new java.io.ByteArrayInputStream((byte[])objectTemp), ((byte[])objectTemp).length);
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
		EncryptedesbBean b = (EncryptedesbBean) eb;
		com.logicacmg.koa.esb.beans.EncryptedesbKey _primaryKey = new com.logicacmg.koa.esb.beans.EncryptedesbKey();
		_primaryKey.stemnummer = b.stemnummer;
		PreparedStatement pstmt;
		pstmt = getPreparedStatement(_removeString);
		try {
			if (_primaryKey.stemnummer == null) {
				pstmt.setNull(1, java.sql.Types.DECIMAL);
			}
			else {
				pstmt.setBigDecimal(1, _primaryKey.stemnummer);
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
		com.logicacmg.koa.esb.beans.EncryptedesbKey key = new com.logicacmg.koa.esb.beans.EncryptedesbKey();
		java.sql.ResultSet resultSet = (java.sql.ResultSet) data;

		if (resultSet != null) {
			Object objectTemp = null;
			key.stemnummer = resultSet.getBigDecimal(1);
			return key;
		}
		return null;
	}
	/**
	 * findByPrimaryKey
	 * @generated
	 */
	public com.logicacmg.koa.esb.beans.Encryptedesb findByPrimaryKey(com.logicacmg.koa.esb.beans.EncryptedesbKey primaryKey) throws java.rmi.RemoteException, javax.ejb.FinderException {
		return (com.logicacmg.koa.esb.beans.Encryptedesb) home.activateBean(primaryKey);
	}
}
