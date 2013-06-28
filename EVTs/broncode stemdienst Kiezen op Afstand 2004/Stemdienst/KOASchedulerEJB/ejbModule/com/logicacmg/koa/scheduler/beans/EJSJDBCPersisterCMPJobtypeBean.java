package com.logicacmg.koa.scheduler.beans;
import com.ibm.ejs.persistence.*;
import javax.ejb.EntityBean;
import java.sql.*;
import java.text.*;
import com.ibm.vap.converters.*;
import com.ibm.vap.converters.streams.*;
/**
 * EJSJDBCPersisterCMPJobtypeBean
 * @generated
 */
public class EJSJDBCPersisterCMPJobtypeBean extends EJSJDBCPersister implements com.logicacmg.koa.scheduler.beans.EJSFinderJobtypeBean {
	/**
	 * @generated
	 */
	private static final String _createString = "INSERT INTO KOA01.JOBTYPE (TYPEID, NAME, FIRSTTIME, INTERVAL, SUCCESSOR, IMPLEMENTATIONCLASS, DEFAULTCONTEXT, PRIORITY) VALUES (?, ?, ?, ?, ?, ?, ?, ?)";
	/**
	 * @generated
	 */
	private static final String _removeString = "DELETE FROM KOA01.JOBTYPE  WHERE TYPEID = ?";
	/**
	 * @generated
	 */
	private static final String _storeString = "UPDATE KOA01.JOBTYPE  SET NAME = ?, FIRSTTIME = ?, INTERVAL = ?, SUCCESSOR = ?, IMPLEMENTATIONCLASS = ?, DEFAULTCONTEXT = ?, PRIORITY = ? WHERE TYPEID = ?";
	/**
	 * @generated
	 */
	private static final String _loadString = "SELECT T1.TYPEID, T1.NAME, T1.FIRSTTIME, T1.INTERVAL, T1.SUCCESSOR, T1.IMPLEMENTATIONCLASS, T1.DEFAULTCONTEXT, T1.PRIORITY FROM KOA01.JOBTYPE  T1 WHERE T1.TYPEID = ?";
	/**
	 * @generated
	 */
	private static final String _loadForUpdateString = _loadString + " FOR UPDATE";
	/**
	 * @generated
	 */
	private byte[] serObj = null;
	/**
	 * EJSJDBCPersisterCMPJobtypeBean
	 * @generated
	 */
	public EJSJDBCPersisterCMPJobtypeBean() throws java.rmi.RemoteException {
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
		JobtypeBean b = (JobtypeBean) eb;
		PreparedStatement pstmt;
		pstmt = getPreparedStatement(_createString);
		try {
			if (b.typeid == null) {
				pstmt.setNull(1, java.sql.Types.DECIMAL);
			}
			else {
				pstmt.setBigDecimal(1, b.typeid);
			}
			if (b.name == null) {
				pstmt.setNull(2, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(2, b.name);
			}
			if (b.firsttime == null) {
				pstmt.setNull(3, java.sql.Types.TIMESTAMP);
			}
			else {
				pstmt.setTimestamp(3, b.firsttime);
			}
			if (b.interval == null) {
				pstmt.setNull(4, java.sql.Types.DECIMAL);
			}
			else {
				pstmt.setBigDecimal(4, b.interval);
			}
			if (b.successor == null) {
				pstmt.setNull(5, java.sql.Types.DECIMAL);
			}
			else {
				pstmt.setBigDecimal(5, b.successor);
			}
			if (b.implementationclass == null) {
				pstmt.setNull(6, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(6, b.implementationclass);
			}
			if (b.defaultcontext == null) {
				pstmt.setNull(7, java.sql.Types.LONGVARCHAR);
			}
			else {
				pstmt.setString(7, b.defaultcontext);
			}
			if (b.priority == null) {
				pstmt.setNull(8, java.sql.Types.INTEGER);
			}
			else {
				pstmt.setInt(8, b.priority.intValue());
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
		JobtypeBean b = (JobtypeBean) eb;
		com.logicacmg.koa.scheduler.beans.JobtypeKey _primaryKey = (com.logicacmg.koa.scheduler.beans.JobtypeKey)pKey;
		java.sql.ResultSet resultSet = (java.sql.ResultSet) data;
		int intTemp;
		b.typeid = _primaryKey.typeid;
		b.name = resultSet.getString(2);
		b.firsttime = resultSet.getTimestamp(3);
		b.interval = resultSet.getBigDecimal(4);
		b.successor = resultSet.getBigDecimal(5);
		b.implementationclass = resultSet.getString(6);
		b.defaultcontext = resultSet.getString(7);
		intTemp = resultSet.getInt(8);
		b.priority = resultSet.wasNull() ? null : new Integer(intTemp);
	}
	/**
	 * load
	 * @generated
	 */
	public void load(EntityBean eb, Object pKey, boolean forUpdate) throws Exception {
		Object objectTemp = null;
		JobtypeBean b = (JobtypeBean) eb;
		com.logicacmg.koa.scheduler.beans.JobtypeKey _primaryKey = (com.logicacmg.koa.scheduler.beans.JobtypeKey)pKey;
		PreparedStatement pstmt;
		ResultSet resultSet = null;
		pstmt = (forUpdate) ?
			getPreparedStatement(_loadForUpdateString):
			getPreparedStatement(_loadString);
		try {
			if (_primaryKey.typeid == null) {
				pstmt.setNull(1, java.sql.Types.DECIMAL);
			}
			else {
				pstmt.setBigDecimal(1, _primaryKey.typeid);
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
		JobtypeBean b = (JobtypeBean) eb;
		com.logicacmg.koa.scheduler.beans.JobtypeKey _primaryKey = new com.logicacmg.koa.scheduler.beans.JobtypeKey();
		_primaryKey.typeid = b.typeid;
		load(b, _primaryKey, forUpdate);
	}
	/**
	 * store
	 * @generated
	 */
	public void store(EntityBean eb) throws Exception {
		Object objectTemp = null;
		JobtypeBean b = (JobtypeBean) eb;
		com.logicacmg.koa.scheduler.beans.JobtypeKey _primaryKey = new com.logicacmg.koa.scheduler.beans.JobtypeKey();
		_primaryKey.typeid = b.typeid;
		PreparedStatement pstmt;
		pstmt = getPreparedStatement(_storeString);
		try {
			if (_primaryKey.typeid == null) {
				pstmt.setNull(8, java.sql.Types.DECIMAL);
			}
			else {
				pstmt.setBigDecimal(8, _primaryKey.typeid);
			}
			if (b.name == null) {
				pstmt.setNull(1, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(1, b.name);
			}
			if (b.firsttime == null) {
				pstmt.setNull(2, java.sql.Types.TIMESTAMP);
			}
			else {
				pstmt.setTimestamp(2, b.firsttime);
			}
			if (b.interval == null) {
				pstmt.setNull(3, java.sql.Types.DECIMAL);
			}
			else {
				pstmt.setBigDecimal(3, b.interval);
			}
			if (b.successor == null) {
				pstmt.setNull(4, java.sql.Types.DECIMAL);
			}
			else {
				pstmt.setBigDecimal(4, b.successor);
			}
			if (b.implementationclass == null) {
				pstmt.setNull(5, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(5, b.implementationclass);
			}
			if (b.defaultcontext == null) {
				pstmt.setNull(6, java.sql.Types.LONGVARCHAR);
			}
			else {
				pstmt.setString(6, b.defaultcontext);
			}
			if (b.priority == null) {
				pstmt.setNull(7, java.sql.Types.INTEGER);
			}
			else {
				pstmt.setInt(7, b.priority.intValue());
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
		JobtypeBean b = (JobtypeBean) eb;
		com.logicacmg.koa.scheduler.beans.JobtypeKey _primaryKey = new com.logicacmg.koa.scheduler.beans.JobtypeKey();
		_primaryKey.typeid = b.typeid;
		PreparedStatement pstmt;
		pstmt = getPreparedStatement(_removeString);
		try {
			if (_primaryKey.typeid == null) {
				pstmt.setNull(1, java.sql.Types.DECIMAL);
			}
			else {
				pstmt.setBigDecimal(1, _primaryKey.typeid);
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
		com.logicacmg.koa.scheduler.beans.JobtypeKey key = new com.logicacmg.koa.scheduler.beans.JobtypeKey();
		java.sql.ResultSet resultSet = (java.sql.ResultSet) data;

		if (resultSet != null) {
			Object objectTemp = null;
			key.typeid = resultSet.getBigDecimal(1);
			return key;
		}
		return null;
	}
	/**
	 * findByPrimaryKey
	 * @generated
	 */
	public com.logicacmg.koa.scheduler.beans.Jobtype findByPrimaryKey(com.logicacmg.koa.scheduler.beans.JobtypeKey primaryKey) throws java.rmi.RemoteException, javax.ejb.FinderException {
		return (com.logicacmg.koa.scheduler.beans.Jobtype) home.activateBean(primaryKey);
	}
}
