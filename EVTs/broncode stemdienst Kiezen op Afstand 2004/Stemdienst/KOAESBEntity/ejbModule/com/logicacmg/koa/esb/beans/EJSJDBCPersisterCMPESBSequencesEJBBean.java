package com.logicacmg.koa.esb.beans;
import com.ibm.ejs.persistence.*;
import javax.ejb.EntityBean;
import java.sql.*;
import java.text.*;
import com.ibm.vap.converters.*;
import com.ibm.vap.converters.streams.*;
/**
 * EJSJDBCPersisterCMPESBSequencesEJBBean
 * @generated
 */
public class EJSJDBCPersisterCMPESBSequencesEJBBean extends EJSJDBCPersister implements com.logicacmg.koa.esb.beans.EJSFinderESBSequencesEJBBean {
	/**
	 * @generated
	 */
	private static final String _createString = "INSERT INTO KOA01.SEQUENCES (TABLENAME, NEXTID) VALUES (?, ?)";
	/**
	 * @generated
	 */
	private static final String _removeString = "DELETE FROM KOA01.SEQUENCES  WHERE TABLENAME = ?";
	/**
	 * @generated
	 */
	private static final String _storeString = "UPDATE KOA01.SEQUENCES  SET NEXTID = ? WHERE TABLENAME = ?";
	/**
	 * @generated
	 */
	private static final String _loadString = "SELECT T1.NEXTID, T1.TABLENAME FROM KOA01.SEQUENCES  T1 WHERE T1.TABLENAME = ?";
	/**
	 * @generated
	 */
	private static final String _loadForUpdateString = _loadString + " FOR UPDATE";
	/**
	 * @generated
	 */
	private byte[] serObj = null;
	/**
	 * EJSJDBCPersisterCMPESBSequencesEJBBean
	 * @generated
	 */
	public EJSJDBCPersisterCMPESBSequencesEJBBean() throws java.rmi.RemoteException {
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
		ESBSequencesEJBBean b = (ESBSequencesEJBBean) eb;
		PreparedStatement pstmt;
		pstmt = getPreparedStatement(_createString);
		try {
			if (b.nextid == null) {
				pstmt.setNull(2, java.sql.Types.DECIMAL);
			}
			else {
				pstmt.setBigDecimal(2, b.nextid);
			}
			if (b.tablename == null) {
				pstmt.setNull(1, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(1, b.tablename);
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
		ESBSequencesEJBBean b = (ESBSequencesEJBBean) eb;
		com.logicacmg.koa.esb.beans.ESBSequencesEJBKey _primaryKey = (com.logicacmg.koa.esb.beans.ESBSequencesEJBKey)pKey;
		java.sql.ResultSet resultSet = (java.sql.ResultSet) data;
		b.tablename = _primaryKey.tablename;
		b.nextid = resultSet.getBigDecimal(1);
	}
	/**
	 * load
	 * @generated
	 */
	public void load(EntityBean eb, Object pKey, boolean forUpdate) throws Exception {
		Object objectTemp = null;
		ESBSequencesEJBBean b = (ESBSequencesEJBBean) eb;
		com.logicacmg.koa.esb.beans.ESBSequencesEJBKey _primaryKey = (com.logicacmg.koa.esb.beans.ESBSequencesEJBKey)pKey;
		PreparedStatement pstmt;
		ResultSet resultSet = null;
		pstmt = (forUpdate) ?
			getPreparedStatement(_loadForUpdateString):
			getPreparedStatement(_loadString);
		try {
			if (_primaryKey.tablename == null) {
				pstmt.setNull(1, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(1, _primaryKey.tablename);
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
		ESBSequencesEJBBean b = (ESBSequencesEJBBean) eb;
		com.logicacmg.koa.esb.beans.ESBSequencesEJBKey _primaryKey = new com.logicacmg.koa.esb.beans.ESBSequencesEJBKey();
		_primaryKey.tablename = b.tablename;
		load(b, _primaryKey, forUpdate);
	}
	/**
	 * store
	 * @generated
	 */
	public void store(EntityBean eb) throws Exception {
		Object objectTemp = null;
		ESBSequencesEJBBean b = (ESBSequencesEJBBean) eb;
		com.logicacmg.koa.esb.beans.ESBSequencesEJBKey _primaryKey = new com.logicacmg.koa.esb.beans.ESBSequencesEJBKey();
		_primaryKey.tablename = b.tablename;
		PreparedStatement pstmt;
		pstmt = getPreparedStatement(_storeString);
		try {
			if (_primaryKey.tablename == null) {
				pstmt.setNull(2, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(2, _primaryKey.tablename);
			}
			if (b.nextid == null) {
				pstmt.setNull(1, java.sql.Types.DECIMAL);
			}
			else {
				pstmt.setBigDecimal(1, b.nextid);
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
		ESBSequencesEJBBean b = (ESBSequencesEJBBean) eb;
		com.logicacmg.koa.esb.beans.ESBSequencesEJBKey _primaryKey = new com.logicacmg.koa.esb.beans.ESBSequencesEJBKey();
		_primaryKey.tablename = b.tablename;
		PreparedStatement pstmt;
		pstmt = getPreparedStatement(_removeString);
		try {
			if (_primaryKey.tablename == null) {
				pstmt.setNull(1, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(1, _primaryKey.tablename);
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
		com.logicacmg.koa.esb.beans.ESBSequencesEJBKey key = new com.logicacmg.koa.esb.beans.ESBSequencesEJBKey();
		java.sql.ResultSet resultSet = (java.sql.ResultSet) data;

		if (resultSet != null) {
			Object objectTemp = null;
			key.tablename = resultSet.getString(2);
			return key;
		}
		return null;
	}
	/**
	 * findByPrimaryKey
	 * @generated
	 */
	public com.logicacmg.koa.esb.beans.ESBSequencesEJB findByPrimaryKey(com.logicacmg.koa.esb.beans.ESBSequencesEJBKey primaryKey) throws java.rmi.RemoteException, javax.ejb.FinderException {
		return (com.logicacmg.koa.esb.beans.ESBSequencesEJB) home.activateBean(primaryKey);
	}
}
