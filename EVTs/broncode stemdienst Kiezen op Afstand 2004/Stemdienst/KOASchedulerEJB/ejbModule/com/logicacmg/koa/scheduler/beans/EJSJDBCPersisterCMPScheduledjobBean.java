package com.logicacmg.koa.scheduler.beans;
import com.ibm.ejs.persistence.*;
import javax.ejb.EntityBean;
import java.sql.*;
import java.text.*;
import com.ibm.vap.converters.*;
import com.ibm.vap.converters.streams.*;
/**
 * EJSJDBCPersisterCMPScheduledjobBean
 * @generated
 */
public class EJSJDBCPersisterCMPScheduledjobBean extends EJSJDBCPersister implements com.logicacmg.koa.scheduler.beans.EJSFinderScheduledjobBean {
	/**
	 * @generated
	 */
	private static final String _createString = "INSERT INTO KOA01.SCHEDULEDJOB (JOBID, STARTTIME, STOPTIME, PRIORITY, STATUS, RETRYCOUNT, LASTUPDATE, CONTEXT, MESSAGE, JOBTYPE) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)";
	/**
	 * @generated
	 */
	private static final String _removeString = "DELETE FROM KOA01.SCHEDULEDJOB  WHERE JOBID = ?";
	/**
	 * @generated
	 */
	private static final String _storeString = "UPDATE KOA01.SCHEDULEDJOB  SET STARTTIME = ?, STOPTIME = ?, PRIORITY = ?, STATUS = ?, RETRYCOUNT = ?, LASTUPDATE = ?, CONTEXT = ?, MESSAGE = ?, JOBTYPE = ? WHERE JOBID = ?";
	/**
	 * @generated
	 */
	private static final String _loadString = "SELECT T1.JOBID, T1.STARTTIME, T1.STOPTIME, T1.PRIORITY, T1.STATUS, T1.RETRYCOUNT, T1.LASTUPDATE, T1.CONTEXT, T1.MESSAGE, T1.JOBTYPE FROM KOA01.SCHEDULEDJOB  T1 WHERE T1.JOBID = ?";
	/**
	 * @generated
	 */
	private static final String _loadForUpdateString = _loadString + " FOR UPDATE";
	/**
	 * @generated
	 */
	private byte[] serObj = null;
	/**
	 * EJSJDBCPersisterCMPScheduledjobBean
	 * @generated
	 */
	public EJSJDBCPersisterCMPScheduledjobBean() throws java.rmi.RemoteException {
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
		ScheduledjobBean b = (ScheduledjobBean) eb;
		PreparedStatement pstmt;
		pstmt = getPreparedStatement(_createString);
		try {
			if (b.jobid == null) {
				pstmt.setNull(1, java.sql.Types.DECIMAL);
			}
			else {
				pstmt.setBigDecimal(1, b.jobid);
			}
			if (b.starttime == null) {
				pstmt.setNull(2, java.sql.Types.TIMESTAMP);
			}
			else {
				pstmt.setTimestamp(2, b.starttime);
			}
			if (b.stoptime == null) {
				pstmt.setNull(3, java.sql.Types.TIMESTAMP);
			}
			else {
				pstmt.setTimestamp(3, b.stoptime);
			}
			if (b.priority == null) {
				pstmt.setNull(4, java.sql.Types.INTEGER);
			}
			else {
				pstmt.setInt(4, b.priority.intValue());
			}
			if (b.status == null) {
				pstmt.setNull(5, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(5, b.status);
			}
			if (b.retrycount == null) {
				pstmt.setNull(6, java.sql.Types.INTEGER);
			}
			else {
				pstmt.setInt(6, b.retrycount.intValue());
			}
			if (b.lastupdate == null) {
				pstmt.setNull(7, java.sql.Types.TIMESTAMP);
			}
			else {
				pstmt.setTimestamp(7, b.lastupdate);
			}
			if (b.context == null) {
				pstmt.setNull(8, java.sql.Types.LONGVARCHAR);
			}
			else {
				pstmt.setString(8, b.context);
			}
			if (b.message == null) {
				pstmt.setNull(9, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(9, b.message);
			}
			if (b.jobtype_typeid == null) {
				pstmt.setNull(10, java.sql.Types.DECIMAL);
			}
			else {
				pstmt.setBigDecimal(10, b.jobtype_typeid);
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
		ScheduledjobBean b = (ScheduledjobBean) eb;
		com.logicacmg.koa.scheduler.beans.ScheduledjobKey _primaryKey = (com.logicacmg.koa.scheduler.beans.ScheduledjobKey)pKey;
		java.sql.ResultSet resultSet = (java.sql.ResultSet) data;
		int intTemp;
		b.jobid = _primaryKey.jobid;
		b.starttime = resultSet.getTimestamp(2);
		b.stoptime = resultSet.getTimestamp(3);
		intTemp = resultSet.getInt(4);
		b.priority = resultSet.wasNull() ? null : new Integer(intTemp);
		b.status = resultSet.getString(5);
		intTemp = resultSet.getInt(6);
		b.retrycount = resultSet.wasNull() ? null : new Integer(intTemp);
		b.lastupdate = resultSet.getTimestamp(7);
		b.context = resultSet.getString(8);
		b.message = resultSet.getString(9);
		b.jobtype_typeid = resultSet.getBigDecimal(10);
	}
	/**
	 * load
	 * @generated
	 */
	public void load(EntityBean eb, Object pKey, boolean forUpdate) throws Exception {
		Object objectTemp = null;
		ScheduledjobBean b = (ScheduledjobBean) eb;
		com.logicacmg.koa.scheduler.beans.ScheduledjobKey _primaryKey = (com.logicacmg.koa.scheduler.beans.ScheduledjobKey)pKey;
		PreparedStatement pstmt;
		ResultSet resultSet = null;
		pstmt = (forUpdate) ?
			getPreparedStatement(_loadForUpdateString):
			getPreparedStatement(_loadString);
		try {
			if (_primaryKey.jobid == null) {
				pstmt.setNull(1, java.sql.Types.DECIMAL);
			}
			else {
				pstmt.setBigDecimal(1, _primaryKey.jobid);
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
		ScheduledjobBean b = (ScheduledjobBean) eb;
		com.logicacmg.koa.scheduler.beans.ScheduledjobKey _primaryKey = new com.logicacmg.koa.scheduler.beans.ScheduledjobKey();
		_primaryKey.jobid = b.jobid;
		load(b, _primaryKey, forUpdate);
	}
	/**
	 * store
	 * @generated
	 */
	public void store(EntityBean eb) throws Exception {
		Object objectTemp = null;
		ScheduledjobBean b = (ScheduledjobBean) eb;
		com.logicacmg.koa.scheduler.beans.ScheduledjobKey _primaryKey = new com.logicacmg.koa.scheduler.beans.ScheduledjobKey();
		_primaryKey.jobid = b.jobid;
		PreparedStatement pstmt;
		pstmt = getPreparedStatement(_storeString);
		try {
			if (_primaryKey.jobid == null) {
				pstmt.setNull(10, java.sql.Types.DECIMAL);
			}
			else {
				pstmt.setBigDecimal(10, _primaryKey.jobid);
			}
			if (b.starttime == null) {
				pstmt.setNull(1, java.sql.Types.TIMESTAMP);
			}
			else {
				pstmt.setTimestamp(1, b.starttime);
			}
			if (b.stoptime == null) {
				pstmt.setNull(2, java.sql.Types.TIMESTAMP);
			}
			else {
				pstmt.setTimestamp(2, b.stoptime);
			}
			if (b.priority == null) {
				pstmt.setNull(3, java.sql.Types.INTEGER);
			}
			else {
				pstmt.setInt(3, b.priority.intValue());
			}
			if (b.status == null) {
				pstmt.setNull(4, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(4, b.status);
			}
			if (b.retrycount == null) {
				pstmt.setNull(5, java.sql.Types.INTEGER);
			}
			else {
				pstmt.setInt(5, b.retrycount.intValue());
			}
			if (b.lastupdate == null) {
				pstmt.setNull(6, java.sql.Types.TIMESTAMP);
			}
			else {
				pstmt.setTimestamp(6, b.lastupdate);
			}
			if (b.context == null) {
				pstmt.setNull(7, java.sql.Types.LONGVARCHAR);
			}
			else {
				pstmt.setString(7, b.context);
			}
			if (b.message == null) {
				pstmt.setNull(8, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(8, b.message);
			}
			if (b.jobtype_typeid == null) {
				pstmt.setNull(9, java.sql.Types.DECIMAL);
			}
			else {
				pstmt.setBigDecimal(9, b.jobtype_typeid);
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
		ScheduledjobBean b = (ScheduledjobBean) eb;
		com.logicacmg.koa.scheduler.beans.ScheduledjobKey _primaryKey = new com.logicacmg.koa.scheduler.beans.ScheduledjobKey();
		_primaryKey.jobid = b.jobid;
		PreparedStatement pstmt;
		pstmt = getPreparedStatement(_removeString);
		try {
			if (_primaryKey.jobid == null) {
				pstmt.setNull(1, java.sql.Types.DECIMAL);
			}
			else {
				pstmt.setBigDecimal(1, _primaryKey.jobid);
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
		com.logicacmg.koa.scheduler.beans.ScheduledjobKey key = new com.logicacmg.koa.scheduler.beans.ScheduledjobKey();
		java.sql.ResultSet resultSet = (java.sql.ResultSet) data;

		if (resultSet != null) {
			Object objectTemp = null;
			key.jobid = resultSet.getBigDecimal(1);
			return key;
		}
		return null;
	}
	/**
	 * findScheduledjobByJobtype
	 * @generated
	 */
	public EJSFinder findScheduledjobByJobtype(com.logicacmg.koa.scheduler.beans.JobtypeKey inKey) throws javax.ejb.FinderException, java.rmi.RemoteException {
		ResultSet resultSet = null;
		PreparedStatement pstmt = null;
		try {
			preFind();
			pstmt = getPreparedStatement("SELECT T1.JOBID, T1.STARTTIME, T1.STOPTIME, T1.PRIORITY, T1.STATUS, T1.RETRYCOUNT, T1.LASTUPDATE, T1.CONTEXT, T1.MESSAGE, T1.JOBTYPE FROM KOA01.SCHEDULEDJOB  T1 WHERE T1.JOBTYPE = ?");
			Object objectTemp = null;
			boolean nullData;
			if (inKey.typeid == null) {
				pstmt.setNull(1, java.sql.Types.DECIMAL);
			}
			else {
				pstmt.setBigDecimal(1, inKey.typeid);
			}
			resultSet = pstmt.executeQuery();
			return new EJSJDBCFinder(resultSet, this, pstmt);
		}
		catch (Exception ex) {
			throw new EJSPersistenceException("find failed:", ex);
		}
	}
	/**
	 * findByPrimaryKey
	 * @generated
	 */
	public com.logicacmg.koa.scheduler.beans.Scheduledjob findByPrimaryKey(com.logicacmg.koa.scheduler.beans.ScheduledjobKey primaryKey) throws java.rmi.RemoteException, javax.ejb.FinderException {
		return (com.logicacmg.koa.scheduler.beans.Scheduledjob) home.activateBean(primaryKey);
	}
}
