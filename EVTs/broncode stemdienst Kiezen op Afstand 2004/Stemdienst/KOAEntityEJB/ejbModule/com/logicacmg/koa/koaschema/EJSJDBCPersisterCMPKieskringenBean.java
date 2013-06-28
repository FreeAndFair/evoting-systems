package com.logicacmg.koa.koaschema;
import com.ibm.ejs.persistence.*;
import javax.ejb.EntityBean;
import java.sql.*;
import java.text.*;
import com.ibm.vap.converters.*;
import com.ibm.vap.converters.streams.*;
/**
 * EJSJDBCPersisterCMPKieskringenBean
 * @generated
 */
public class EJSJDBCPersisterCMPKieskringenBean extends EJSJDBCPersister implements com.logicacmg.koa.koaschema.EJSFinderKieskringenBean {
	/**
	 * @generated
	 */
	private static final String _createString = "INSERT INTO KOA01.KIESKRINGEN (KIESKRINGNUMMER, KIESKRINGNAAM) VALUES (?, ?)";
	/**
	 * @generated
	 */
	private static final String _removeString = "DELETE FROM KOA01.KIESKRINGEN  WHERE KIESKRINGNUMMER = ?";
	/**
	 * @generated
	 */
	private static final String _storeString = "UPDATE KOA01.KIESKRINGEN  SET KIESKRINGNAAM = ? WHERE KIESKRINGNUMMER = ?";
	/**
	 * @generated
	 */
	private static final String _loadString = "SELECT T1.KIESKRINGNUMMER, T1.KIESKRINGNAAM FROM KOA01.KIESKRINGEN  T1 WHERE T1.KIESKRINGNUMMER = ?";
	/**
	 * @generated
	 */
	private static final String _loadForUpdateString = _loadString + " FOR UPDATE";
	/**
	 * @generated
	 */
	private byte[] serObj = null;
	/**
	 * EJSJDBCPersisterCMPKieskringenBean
	 * @generated
	 */
	public EJSJDBCPersisterCMPKieskringenBean() throws java.rmi.RemoteException {
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
		KieskringenBean b = (KieskringenBean) eb;
		PreparedStatement pstmt;
		pstmt = getPreparedStatement(_createString);
		try {
			if (b.kieskringnummer == null) {
				pstmt.setNull(1, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(1, b.kieskringnummer);
			}
			if (b.kieskringnaam == null) {
				pstmt.setNull(2, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(2, b.kieskringnaam);
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
		KieskringenBean b = (KieskringenBean) eb;
		com.logicacmg.koa.koaschema.KieskringenKey _primaryKey = (com.logicacmg.koa.koaschema.KieskringenKey)pKey;
		java.sql.ResultSet resultSet = (java.sql.ResultSet) data;
		b.kieskringnummer = _primaryKey.kieskringnummer;
		b.kieskringnaam = resultSet.getString(2);
	}
	/**
	 * load
	 * @generated
	 */
	public void load(EntityBean eb, Object pKey, boolean forUpdate) throws Exception {
		Object objectTemp = null;
		KieskringenBean b = (KieskringenBean) eb;
		com.logicacmg.koa.koaschema.KieskringenKey _primaryKey = (com.logicacmg.koa.koaschema.KieskringenKey)pKey;
		PreparedStatement pstmt;
		ResultSet resultSet = null;
		pstmt = (forUpdate) ?
			getPreparedStatement(_loadForUpdateString):
			getPreparedStatement(_loadString);
		try {
			if (_primaryKey.kieskringnummer == null) {
				pstmt.setNull(1, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(1, _primaryKey.kieskringnummer);
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
		KieskringenBean b = (KieskringenBean) eb;
		com.logicacmg.koa.koaschema.KieskringenKey _primaryKey = new com.logicacmg.koa.koaschema.KieskringenKey();
		_primaryKey.kieskringnummer = b.kieskringnummer;
		load(b, _primaryKey, forUpdate);
	}
	/**
	 * store
	 * @generated
	 */
	public void store(EntityBean eb) throws Exception {
		Object objectTemp = null;
		KieskringenBean b = (KieskringenBean) eb;
		com.logicacmg.koa.koaschema.KieskringenKey _primaryKey = new com.logicacmg.koa.koaschema.KieskringenKey();
		_primaryKey.kieskringnummer = b.kieskringnummer;
		PreparedStatement pstmt;
		pstmt = getPreparedStatement(_storeString);
		try {
			if (_primaryKey.kieskringnummer == null) {
				pstmt.setNull(2, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(2, _primaryKey.kieskringnummer);
			}
			if (b.kieskringnaam == null) {
				pstmt.setNull(1, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(1, b.kieskringnaam);
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
		KieskringenBean b = (KieskringenBean) eb;
		com.logicacmg.koa.koaschema.KieskringenKey _primaryKey = new com.logicacmg.koa.koaschema.KieskringenKey();
		_primaryKey.kieskringnummer = b.kieskringnummer;
		PreparedStatement pstmt;
		pstmt = getPreparedStatement(_removeString);
		try {
			if (_primaryKey.kieskringnummer == null) {
				pstmt.setNull(1, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(1, _primaryKey.kieskringnummer);
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
		com.logicacmg.koa.koaschema.KieskringenKey key = new com.logicacmg.koa.koaschema.KieskringenKey();
		java.sql.ResultSet resultSet = (java.sql.ResultSet) data;

		if (resultSet != null) {
			Object objectTemp = null;
			key.kieskringnummer = resultSet.getString(1);
			return key;
		}
		return null;
	}
	/**
	 * findByPrimaryKey
	 * @generated
	 */
	public com.logicacmg.koa.koaschema.Kieskringen findByPrimaryKey(com.logicacmg.koa.koaschema.KieskringenKey primaryKey) throws java.rmi.RemoteException, javax.ejb.FinderException {
		return (com.logicacmg.koa.koaschema.Kieskringen) home.activateBean(primaryKey);
	}
}
