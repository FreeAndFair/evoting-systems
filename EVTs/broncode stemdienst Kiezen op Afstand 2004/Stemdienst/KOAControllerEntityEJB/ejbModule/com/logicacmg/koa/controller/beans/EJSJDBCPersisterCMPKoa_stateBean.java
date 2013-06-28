package com.logicacmg.koa.controller.beans;
import com.ibm.ejs.persistence.*;
import javax.ejb.EntityBean;
import java.sql.*;
import java.text.*;
import com.ibm.vap.converters.*;
import com.ibm.vap.converters.streams.*;
/**
 * EJSJDBCPersisterCMPKoa_stateBean
 * @generated
 */
public class EJSJDBCPersisterCMPKoa_stateBean extends EJSJDBCPersister implements com.logicacmg.koa.controller.beans.EJSFinderKoa_stateBean {
	/**
	 * @generated
	 */
	private static final String _createString = "INSERT INTO KOA01.KOA_STATE (ID, CURRENT_STATE) VALUES (?, ?)";
	/**
	 * @generated
	 */
	private static final String _removeString = "DELETE FROM KOA01.KOA_STATE  WHERE ID = ?";
	/**
	 * @generated
	 */
	private static final String _storeString = "UPDATE KOA01.KOA_STATE  SET CURRENT_STATE = ? WHERE ID = ?";
	/**
	 * @generated
	 */
	private static final String _loadString = "SELECT T1.ID, T1.CURRENT_STATE FROM KOA01.KOA_STATE  T1 WHERE T1.ID = ?";
	/**
	 * @generated
	 */
	private static final String _loadForUpdateString = _loadString + " FOR UPDATE";
	/**
	 * @generated
	 */
	private byte[] serObj = null;
	/**
	 * EJSJDBCPersisterCMPKoa_stateBean
	 * @generated
	 */
	public EJSJDBCPersisterCMPKoa_stateBean() throws java.rmi.RemoteException {
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
		Koa_stateBean b = (Koa_stateBean) eb;
		PreparedStatement pstmt;
		pstmt = getPreparedStatement(_createString);
		try {
			if (b.id == null) {
				pstmt.setNull(1, java.sql.Types.INTEGER);
			}
			else {
				pstmt.setInt(1, b.id.intValue());
			}
			if (b.current_state == null) {
				pstmt.setNull(2, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(2, b.current_state);
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
		Koa_stateBean b = (Koa_stateBean) eb;
		com.logicacmg.koa.controller.beans.Koa_stateKey _primaryKey = (com.logicacmg.koa.controller.beans.Koa_stateKey)pKey;
		java.sql.ResultSet resultSet = (java.sql.ResultSet) data;
		b.id = _primaryKey.id;
		b.current_state = resultSet.getString(2);
	}
	/**
	 * load
	 * @generated
	 */
	public void load(EntityBean eb, Object pKey, boolean forUpdate) throws Exception {
		Object objectTemp = null;
		Koa_stateBean b = (Koa_stateBean) eb;
		com.logicacmg.koa.controller.beans.Koa_stateKey _primaryKey = (com.logicacmg.koa.controller.beans.Koa_stateKey)pKey;
		PreparedStatement pstmt;
		ResultSet resultSet = null;
		pstmt = (forUpdate) ?
			getPreparedStatement(_loadForUpdateString):
			getPreparedStatement(_loadString);
		try {
			if (_primaryKey.id == null) {
				pstmt.setNull(1, java.sql.Types.INTEGER);
			}
			else {
				pstmt.setInt(1, _primaryKey.id.intValue());
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
		Koa_stateBean b = (Koa_stateBean) eb;
		com.logicacmg.koa.controller.beans.Koa_stateKey _primaryKey = new com.logicacmg.koa.controller.beans.Koa_stateKey();
		_primaryKey.id = b.id;
		load(b, _primaryKey, forUpdate);
	}
	/**
	 * store
	 * @generated
	 */
	public void store(EntityBean eb) throws Exception {
		Object objectTemp = null;
		Koa_stateBean b = (Koa_stateBean) eb;
		com.logicacmg.koa.controller.beans.Koa_stateKey _primaryKey = new com.logicacmg.koa.controller.beans.Koa_stateKey();
		_primaryKey.id = b.id;
		PreparedStatement pstmt;
		pstmt = getPreparedStatement(_storeString);
		try {
			if (_primaryKey.id == null) {
				pstmt.setNull(2, java.sql.Types.INTEGER);
			}
			else {
				pstmt.setInt(2, _primaryKey.id.intValue());
			}
			if (b.current_state == null) {
				pstmt.setNull(1, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(1, b.current_state);
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
		Koa_stateBean b = (Koa_stateBean) eb;
		com.logicacmg.koa.controller.beans.Koa_stateKey _primaryKey = new com.logicacmg.koa.controller.beans.Koa_stateKey();
		_primaryKey.id = b.id;
		PreparedStatement pstmt;
		pstmt = getPreparedStatement(_removeString);
		try {
			if (_primaryKey.id == null) {
				pstmt.setNull(1, java.sql.Types.INTEGER);
			}
			else {
				pstmt.setInt(1, _primaryKey.id.intValue());
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
		com.logicacmg.koa.controller.beans.Koa_stateKey key = new com.logicacmg.koa.controller.beans.Koa_stateKey();
		java.sql.ResultSet resultSet = (java.sql.ResultSet) data;

		if (resultSet != null) {
			Object objectTemp = null;
			int intTemp;
			intTemp = resultSet.getInt(1);
			key.id = resultSet.wasNull() ? null : new Integer(intTemp);
			return key;
		}
		return null;
	}
	/**
	 * findByPrimaryKey
	 * @generated
	 */
	public com.logicacmg.koa.controller.beans.Koa_state findByPrimaryKey(com.logicacmg.koa.controller.beans.Koa_stateKey primaryKey) throws java.rmi.RemoteException, javax.ejb.FinderException {
		return (com.logicacmg.koa.controller.beans.Koa_state) home.activateBean(primaryKey);
	}
}
