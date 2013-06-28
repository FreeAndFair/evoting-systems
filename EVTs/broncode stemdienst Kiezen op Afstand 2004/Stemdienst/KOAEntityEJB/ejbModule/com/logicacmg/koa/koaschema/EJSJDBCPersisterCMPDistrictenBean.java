package com.logicacmg.koa.koaschema;
import com.ibm.ejs.persistence.*;
import javax.ejb.EntityBean;
import java.sql.*;
import java.text.*;
import com.ibm.vap.converters.*;
import com.ibm.vap.converters.streams.*;
/**
 * EJSJDBCPersisterCMPDistrictenBean
 * @generated
 */
public class EJSJDBCPersisterCMPDistrictenBean extends EJSJDBCPersister implements com.logicacmg.koa.koaschema.EJSFinderDistrictenBean {
	/**
	 * @generated
	 */
	private static final String _createString = "INSERT INTO KOA01.DISTRICTEN (DISTRICTNUMMER, DISTRICTNAAM, KIESKRINGNUMMER) VALUES (?, ?, ?)";
	/**
	 * @generated
	 */
	private static final String _removeString = "DELETE FROM KOA01.DISTRICTEN  WHERE DISTRICTNUMMER = ?";
	/**
	 * @generated
	 */
	private static final String _storeString = "UPDATE KOA01.DISTRICTEN  SET DISTRICTNAAM = ?, KIESKRINGNUMMER = ? WHERE DISTRICTNUMMER = ?";
	/**
	 * @generated
	 */
	private static final String _loadString = "SELECT T1.DISTRICTNUMMER, T1.DISTRICTNAAM, T1.KIESKRINGNUMMER FROM KOA01.DISTRICTEN  T1 WHERE T1.DISTRICTNUMMER = ?";
	/**
	 * @generated
	 */
	private static final String _loadForUpdateString = _loadString + " FOR UPDATE";
	/**
	 * @generated
	 */
	private byte[] serObj = null;
	/**
	 * EJSJDBCPersisterCMPDistrictenBean
	 * @generated
	 */
	public EJSJDBCPersisterCMPDistrictenBean() throws java.rmi.RemoteException {
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
		DistrictenBean b = (DistrictenBean) eb;
		PreparedStatement pstmt;
		pstmt = getPreparedStatement(_createString);
		try {
			if (b.districtnummer == null) {
				pstmt.setNull(1, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(1, b.districtnummer);
			}
			if (b.districtnaam == null) {
				pstmt.setNull(2, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(2, b.districtnaam);
			}
			if (b.fk_dist_kkr_kieskringnummer == null) {
				pstmt.setNull(3, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(3, b.fk_dist_kkr_kieskringnummer);
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
		DistrictenBean b = (DistrictenBean) eb;
		com.logicacmg.koa.koaschema.DistrictenKey _primaryKey = (com.logicacmg.koa.koaschema.DistrictenKey)pKey;
		java.sql.ResultSet resultSet = (java.sql.ResultSet) data;
		b.districtnummer = _primaryKey.districtnummer;
		b.districtnaam = resultSet.getString(2);
		b.fk_dist_kkr_kieskringnummer = resultSet.getString(3);
	}
	/**
	 * load
	 * @generated
	 */
	public void load(EntityBean eb, Object pKey, boolean forUpdate) throws Exception {
		Object objectTemp = null;
		DistrictenBean b = (DistrictenBean) eb;
		com.logicacmg.koa.koaschema.DistrictenKey _primaryKey = (com.logicacmg.koa.koaschema.DistrictenKey)pKey;
		PreparedStatement pstmt;
		ResultSet resultSet = null;
		pstmt = (forUpdate) ?
			getPreparedStatement(_loadForUpdateString):
			getPreparedStatement(_loadString);
		try {
			if (_primaryKey.districtnummer == null) {
				pstmt.setNull(1, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(1, _primaryKey.districtnummer);
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
		DistrictenBean b = (DistrictenBean) eb;
		com.logicacmg.koa.koaschema.DistrictenKey _primaryKey = new com.logicacmg.koa.koaschema.DistrictenKey();
		_primaryKey.districtnummer = b.districtnummer;
		load(b, _primaryKey, forUpdate);
	}
	/**
	 * store
	 * @generated
	 */
	public void store(EntityBean eb) throws Exception {
		Object objectTemp = null;
		DistrictenBean b = (DistrictenBean) eb;
		com.logicacmg.koa.koaschema.DistrictenKey _primaryKey = new com.logicacmg.koa.koaschema.DistrictenKey();
		_primaryKey.districtnummer = b.districtnummer;
		PreparedStatement pstmt;
		pstmt = getPreparedStatement(_storeString);
		try {
			if (_primaryKey.districtnummer == null) {
				pstmt.setNull(3, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(3, _primaryKey.districtnummer);
			}
			if (b.districtnaam == null) {
				pstmt.setNull(1, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(1, b.districtnaam);
			}
			if (b.fk_dist_kkr_kieskringnummer == null) {
				pstmt.setNull(2, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(2, b.fk_dist_kkr_kieskringnummer);
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
		DistrictenBean b = (DistrictenBean) eb;
		com.logicacmg.koa.koaschema.DistrictenKey _primaryKey = new com.logicacmg.koa.koaschema.DistrictenKey();
		_primaryKey.districtnummer = b.districtnummer;
		PreparedStatement pstmt;
		pstmt = getPreparedStatement(_removeString);
		try {
			if (_primaryKey.districtnummer == null) {
				pstmt.setNull(1, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(1, _primaryKey.districtnummer);
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
		com.logicacmg.koa.koaschema.DistrictenKey key = new com.logicacmg.koa.koaschema.DistrictenKey();
		java.sql.ResultSet resultSet = (java.sql.ResultSet) data;

		if (resultSet != null) {
			Object objectTemp = null;
			key.districtnummer = resultSet.getString(1);
			return key;
		}
		return null;
	}
	/**
	 * findDistrictenByFk_dist_kkr
	 * @generated
	 */
	public EJSFinder findDistrictenByFk_dist_kkr(com.logicacmg.koa.koaschema.KieskringenKey inKey) throws javax.ejb.FinderException, java.rmi.RemoteException {
		ResultSet resultSet = null;
		PreparedStatement pstmt = null;
		try {
			preFind();
			pstmt = getPreparedStatement("SELECT T1.DISTRICTNUMMER, T1.DISTRICTNAAM, T1.KIESKRINGNUMMER FROM KOA01.DISTRICTEN  T1 WHERE T1.KIESKRINGNUMMER = ?");
			Object objectTemp = null;
			boolean nullData;
			if (inKey.kieskringnummer == null) {
				pstmt.setNull(1, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(1, inKey.kieskringnummer);
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
	public com.logicacmg.koa.koaschema.Districten findByPrimaryKey(com.logicacmg.koa.koaschema.DistrictenKey primaryKey) throws java.rmi.RemoteException, javax.ejb.FinderException {
		return (com.logicacmg.koa.koaschema.Districten) home.activateBean(primaryKey);
	}
}
