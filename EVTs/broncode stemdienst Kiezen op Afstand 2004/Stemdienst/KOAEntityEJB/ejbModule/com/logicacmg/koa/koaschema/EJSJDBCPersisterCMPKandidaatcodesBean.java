package com.logicacmg.koa.koaschema;
import com.ibm.ejs.persistence.*;
import javax.ejb.EntityBean;
import java.sql.*;
import java.text.*;
import com.ibm.vap.converters.*;
import com.ibm.vap.converters.streams.*;
/**
 * EJSJDBCPersisterCMPKandidaatcodesBean
 * @generated
 */
public class EJSJDBCPersisterCMPKandidaatcodesBean extends EJSJDBCPersister implements com.logicacmg.koa.koaschema.EJSFinderKandidaatcodesBean {
	/**
	 * @generated
	 */
	private static final String _createString = "INSERT INTO KOA01.KANDIDAATCODES (KANDIDAATCODE, KIESKRINGNUMMER, KIESLIJSTNUMMER, POSITIENUMMER) VALUES (?, ?, ?, ?)";
	/**
	 * @generated
	 */
	private static final String _removeString = "DELETE FROM KOA01.KANDIDAATCODES  WHERE KANDIDAATCODE = ?";
	/**
	 * @generated
	 */
	private static final String _storeString = "UPDATE KOA01.KANDIDAATCODES  SET KIESKRINGNUMMER = ?, KIESLIJSTNUMMER = ?, POSITIENUMMER = ? WHERE KANDIDAATCODE = ?";
	/**
	 * @generated
	 */
	private static final String _loadString = "SELECT T1.KANDIDAATCODE, T1.KIESKRINGNUMMER, T1.KIESLIJSTNUMMER, T1.POSITIENUMMER FROM KOA01.KANDIDAATCODES  T1 WHERE T1.KANDIDAATCODE = ?";
	/**
	 * @generated
	 */
	private static final String _loadForUpdateString = _loadString + " FOR UPDATE";
	/**
	 * @generated
	 */
	private byte[] serObj = null;
	/**
	 * EJSJDBCPersisterCMPKandidaatcodesBean
	 * @generated
	 */
	public EJSJDBCPersisterCMPKandidaatcodesBean() throws java.rmi.RemoteException {
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
		KandidaatcodesBean b = (KandidaatcodesBean) eb;
		PreparedStatement pstmt;
		pstmt = getPreparedStatement(_createString);
		try {
			if (b.kandidaatcode == null) {
				pstmt.setNull(1, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(1, b.kandidaatcode);
			}
			if (b.fk_kkrklpn_1_positienummer == null) {
				pstmt.setNull(4, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(4, b.fk_kkrklpn_1_positienummer);
			}
			if (b.fk_kkrklpn_1_fk_klkr_1_kieslijstnummer == null) {
				pstmt.setNull(3, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(3, b.fk_kkrklpn_1_fk_klkr_1_kieslijstnummer);
			}
			if (b.fk_kkrklpn_1_fk_klkr_1_fk_kkr_1_kieskringnummer == null) {
				pstmt.setNull(2, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(2, b.fk_kkrklpn_1_fk_klkr_1_fk_kkr_1_kieskringnummer);
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
		KandidaatcodesBean b = (KandidaatcodesBean) eb;
		com.logicacmg.koa.koaschema.KandidaatcodesKey _primaryKey = (com.logicacmg.koa.koaschema.KandidaatcodesKey)pKey;
		java.sql.ResultSet resultSet = (java.sql.ResultSet) data;
		b.kandidaatcode = _primaryKey.kandidaatcode;
		b.fk_kkrklpn_1_positienummer = resultSet.getString(4);
		b.fk_kkrklpn_1_fk_klkr_1_kieslijstnummer = resultSet.getString(3);
		b.fk_kkrklpn_1_fk_klkr_1_fk_kkr_1_kieskringnummer = resultSet.getString(2);
	}
	/**
	 * load
	 * @generated
	 */
	public void load(EntityBean eb, Object pKey, boolean forUpdate) throws Exception {
		Object objectTemp = null;
		KandidaatcodesBean b = (KandidaatcodesBean) eb;
		com.logicacmg.koa.koaschema.KandidaatcodesKey _primaryKey = (com.logicacmg.koa.koaschema.KandidaatcodesKey)pKey;
		PreparedStatement pstmt;
		ResultSet resultSet = null;
		pstmt = (forUpdate) ?
			getPreparedStatement(_loadForUpdateString):
			getPreparedStatement(_loadString);
		try {
			if (_primaryKey.kandidaatcode == null) {
				pstmt.setNull(1, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(1, _primaryKey.kandidaatcode);
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
		KandidaatcodesBean b = (KandidaatcodesBean) eb;
		com.logicacmg.koa.koaschema.KandidaatcodesKey _primaryKey = new com.logicacmg.koa.koaschema.KandidaatcodesKey();
		_primaryKey.kandidaatcode = b.kandidaatcode;
		load(b, _primaryKey, forUpdate);
	}
	/**
	 * store
	 * @generated
	 */
	public void store(EntityBean eb) throws Exception {
		Object objectTemp = null;
		KandidaatcodesBean b = (KandidaatcodesBean) eb;
		com.logicacmg.koa.koaschema.KandidaatcodesKey _primaryKey = new com.logicacmg.koa.koaschema.KandidaatcodesKey();
		_primaryKey.kandidaatcode = b.kandidaatcode;
		PreparedStatement pstmt;
		pstmt = getPreparedStatement(_storeString);
		try {
			if (_primaryKey.kandidaatcode == null) {
				pstmt.setNull(4, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(4, _primaryKey.kandidaatcode);
			}
			if (b.fk_kkrklpn_1_positienummer == null) {
				pstmt.setNull(3, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(3, b.fk_kkrklpn_1_positienummer);
			}
			if (b.fk_kkrklpn_1_fk_klkr_1_kieslijstnummer == null) {
				pstmt.setNull(2, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(2, b.fk_kkrklpn_1_fk_klkr_1_kieslijstnummer);
			}
			if (b.fk_kkrklpn_1_fk_klkr_1_fk_kkr_1_kieskringnummer == null) {
				pstmt.setNull(1, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(1, b.fk_kkrklpn_1_fk_klkr_1_fk_kkr_1_kieskringnummer);
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
		KandidaatcodesBean b = (KandidaatcodesBean) eb;
		com.logicacmg.koa.koaschema.KandidaatcodesKey _primaryKey = new com.logicacmg.koa.koaschema.KandidaatcodesKey();
		_primaryKey.kandidaatcode = b.kandidaatcode;
		PreparedStatement pstmt;
		pstmt = getPreparedStatement(_removeString);
		try {
			if (_primaryKey.kandidaatcode == null) {
				pstmt.setNull(1, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(1, _primaryKey.kandidaatcode);
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
		com.logicacmg.koa.koaschema.KandidaatcodesKey key = new com.logicacmg.koa.koaschema.KandidaatcodesKey();
		java.sql.ResultSet resultSet = (java.sql.ResultSet) data;

		if (resultSet != null) {
			Object objectTemp = null;
			key.kandidaatcode = resultSet.getString(1);
			return key;
		}
		return null;
	}
	/**
	 * findByPrimaryKey
	 * @generated
	 */
	public com.logicacmg.koa.koaschema.Kandidaatcodes findByPrimaryKey(com.logicacmg.koa.koaschema.KandidaatcodesKey primaryKey) throws java.rmi.RemoteException, javax.ejb.FinderException {
		return (com.logicacmg.koa.koaschema.Kandidaatcodes) home.activateBean(primaryKey);
	}
	/**
	 * findKandidaatcodesByFk_kkrklpn_1
	 * @generated
	 */
	public EJSFinder findKandidaatcodesByFk_kkrklpn_1(com.logicacmg.koa.koaschema.LijstpositiesKey inKey) throws javax.ejb.FinderException, java.rmi.RemoteException {
		ResultSet resultSet = null;
		PreparedStatement pstmt = null;
		try {
			preFind();
			pstmt = getPreparedStatement("SELECT T1.KANDIDAATCODE, T1.KIESKRINGNUMMER, T1.KIESLIJSTNUMMER, T1.POSITIENUMMER FROM KOA01.KANDIDAATCODES  T1 WHERE T1.KIESKRINGNUMMER = ? AND T1.KIESLIJSTNUMMER = ? AND T1.POSITIENUMMER = ?");
			Object objectTemp = null;
			boolean nullData;
			if (inKey.positienummer == null) {
				pstmt.setNull(3, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(3, inKey.positienummer);
			}
			if (inKey.fk_klkr_1_kieslijstnummer == null) {
				pstmt.setNull(2, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(2, inKey.fk_klkr_1_kieslijstnummer);
			}
			if (inKey.fk_klkr_1_fk_kkr_1_kieskringnummer == null) {
				pstmt.setNull(1, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(1, inKey.fk_klkr_1_fk_kkr_1_kieskringnummer);
			}
			resultSet = pstmt.executeQuery();
			return new EJSJDBCFinder(resultSet, this, pstmt);
		}
		catch (Exception ex) {
			throw new EJSPersistenceException("find failed:", ex);
		}
	}
}
