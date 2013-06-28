package com.logicacmg.koa.koaschema;
import com.ibm.ejs.persistence.*;
import javax.ejb.EntityBean;
import java.sql.*;
import java.text.*;
import com.ibm.vap.converters.*;
import com.ibm.vap.converters.streams.*;
/**
 * EJSJDBCPersisterCMPKieslijstenBean
 * @generated
 */
public class EJSJDBCPersisterCMPKieslijstenBean extends EJSJDBCPersister implements com.logicacmg.koa.koaschema.EJSFinderKieslijstenBean {
	/**
	 * @generated
	 */
	private static final String _createString = "INSERT INTO KOA01.KIESLIJSTEN (KIESLIJSTNUMMER, KIESKRINGNUMMER, LIJSTNAAM) VALUES (?, ?, ?)";
	/**
	 * @generated
	 */
	private static final String _removeString = "DELETE FROM KOA01.KIESLIJSTEN  WHERE KIESLIJSTNUMMER = ? AND KIESKRINGNUMMER = ?";
	/**
	 * @generated
	 */
	private static final String _storeString = "UPDATE KOA01.KIESLIJSTEN  SET LIJSTNAAM = ? WHERE KIESLIJSTNUMMER = ? AND KIESKRINGNUMMER = ?";
	/**
	 * @generated
	 */
	private static final String _loadString = "SELECT T1.KIESLIJSTNUMMER, T1.LIJSTNAAM, T1.KIESKRINGNUMMER FROM KOA01.KIESLIJSTEN  T1 WHERE T1.KIESLIJSTNUMMER = ? AND T1.KIESKRINGNUMMER = ?";
	/**
	 * @generated
	 */
	private static final String _loadForUpdateString = _loadString + " FOR UPDATE";
	/**
	 * @generated
	 */
	private byte[] serObj = null;
	/**
	 * EJSJDBCPersisterCMPKieslijstenBean
	 * @generated
	 */
	public EJSJDBCPersisterCMPKieslijstenBean() throws java.rmi.RemoteException {
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
		KieslijstenBean b = (KieslijstenBean) eb;
		PreparedStatement pstmt;
		pstmt = getPreparedStatement(_createString);
		try {
			if (b.kieslijstnummer == null) {
				pstmt.setNull(1, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(1, b.kieslijstnummer);
			}
			if (b.lijstnaam == null) {
				pstmt.setNull(3, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(3, b.lijstnaam);
			}
			if (b.fk_kkr_1_kieskringnummer == null) {
				pstmt.setNull(2, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(2, b.fk_kkr_1_kieskringnummer);
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
		KieslijstenBean b = (KieslijstenBean) eb;
		com.logicacmg.koa.koaschema.KieslijstenKey _primaryKey = (com.logicacmg.koa.koaschema.KieslijstenKey)pKey;
		java.sql.ResultSet resultSet = (java.sql.ResultSet) data;
		b.kieslijstnummer = _primaryKey.kieslijstnummer;
		b.fk_kkr_1_kieskringnummer = _primaryKey.fk_kkr_1_kieskringnummer;
		b.lijstnaam = resultSet.getString(2);
		b.fk_kkr_1_kieskringnummer = resultSet.getString(3);
	}
	/**
	 * load
	 * @generated
	 */
	public void load(EntityBean eb, Object pKey, boolean forUpdate) throws Exception {
		Object objectTemp = null;
		KieslijstenBean b = (KieslijstenBean) eb;
		com.logicacmg.koa.koaschema.KieslijstenKey _primaryKey = (com.logicacmg.koa.koaschema.KieslijstenKey)pKey;
		PreparedStatement pstmt;
		ResultSet resultSet = null;
		pstmt = (forUpdate) ?
			getPreparedStatement(_loadForUpdateString):
			getPreparedStatement(_loadString);
		try {
			if (_primaryKey.kieslijstnummer == null) {
				pstmt.setNull(1, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(1, _primaryKey.kieslijstnummer);
			}
			if (_primaryKey.fk_kkr_1_kieskringnummer == null) {
				pstmt.setNull(2, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(2, _primaryKey.fk_kkr_1_kieskringnummer);
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
		KieslijstenBean b = (KieslijstenBean) eb;
		com.logicacmg.koa.koaschema.KieslijstenKey _primaryKey = new com.logicacmg.koa.koaschema.KieslijstenKey();
		_primaryKey.kieslijstnummer = b.kieslijstnummer;
		_primaryKey.fk_kkr_1_kieskringnummer = b.fk_kkr_1_kieskringnummer;
		load(b, _primaryKey, forUpdate);
	}
	/**
	 * store
	 * @generated
	 */
	public void store(EntityBean eb) throws Exception {
		Object objectTemp = null;
		KieslijstenBean b = (KieslijstenBean) eb;
		com.logicacmg.koa.koaschema.KieslijstenKey _primaryKey = new com.logicacmg.koa.koaschema.KieslijstenKey();
		_primaryKey.kieslijstnummer = b.kieslijstnummer;
		_primaryKey.fk_kkr_1_kieskringnummer = b.fk_kkr_1_kieskringnummer;
		PreparedStatement pstmt;
		pstmt = getPreparedStatement(_storeString);
		try {
			if (_primaryKey.kieslijstnummer == null) {
				pstmt.setNull(2, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(2, _primaryKey.kieslijstnummer);
			}
			if (_primaryKey.fk_kkr_1_kieskringnummer == null) {
				pstmt.setNull(3, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(3, _primaryKey.fk_kkr_1_kieskringnummer);
			}
			if (b.lijstnaam == null) {
				pstmt.setNull(1, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(1, b.lijstnaam);
			}
			if (b.fk_kkr_1_kieskringnummer == null) {
				pstmt.setNull(3, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(3, b.fk_kkr_1_kieskringnummer);
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
		KieslijstenBean b = (KieslijstenBean) eb;
		com.logicacmg.koa.koaschema.KieslijstenKey _primaryKey = new com.logicacmg.koa.koaschema.KieslijstenKey();
		_primaryKey.kieslijstnummer = b.kieslijstnummer;
		_primaryKey.fk_kkr_1_kieskringnummer = b.fk_kkr_1_kieskringnummer;
		PreparedStatement pstmt;
		pstmt = getPreparedStatement(_removeString);
		try {
			if (_primaryKey.kieslijstnummer == null) {
				pstmt.setNull(1, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(1, _primaryKey.kieslijstnummer);
			}
			if (_primaryKey.fk_kkr_1_kieskringnummer == null) {
				pstmt.setNull(2, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(2, _primaryKey.fk_kkr_1_kieskringnummer);
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
		com.logicacmg.koa.koaschema.KieslijstenKey key = new com.logicacmg.koa.koaschema.KieslijstenKey();
		java.sql.ResultSet resultSet = (java.sql.ResultSet) data;

		if (resultSet != null) {
			Object objectTemp = null;
			key.kieslijstnummer = resultSet.getString(1);
			key.fk_kkr_1_kieskringnummer = resultSet.getString(3);
			return key;
		}
		return null;
	}
	/**
	 * findKieslijstenByFk_kkr_1
	 * @generated
	 */
	public EJSFinder findKieslijstenByFk_kkr_1(com.logicacmg.koa.koaschema.KieskringenKey inKey) throws javax.ejb.FinderException, java.rmi.RemoteException {
		ResultSet resultSet = null;
		PreparedStatement pstmt = null;
		try {
			preFind();
			pstmt = getPreparedStatement("SELECT T1.KIESLIJSTNUMMER, T1.LIJSTNAAM, T1.KIESKRINGNUMMER FROM KOA01.KIESLIJSTEN  T1 WHERE T1.KIESKRINGNUMMER = ?");
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
	public com.logicacmg.koa.koaschema.Kieslijsten findByPrimaryKey(com.logicacmg.koa.koaschema.KieslijstenKey primaryKey) throws java.rmi.RemoteException, javax.ejb.FinderException {
		return (com.logicacmg.koa.koaschema.Kieslijsten) home.activateBean(primaryKey);
	}
}
