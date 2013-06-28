package com.logicacmg.koa.koaschema;
import com.ibm.ejs.persistence.*;
import javax.ejb.EntityBean;
import java.sql.*;
import java.text.*;
import com.ibm.vap.converters.*;
import com.ibm.vap.converters.streams.*;
/**
 * EJSJDBCPersisterCMPLijstpositiesBean
 * @generated
 */
public class EJSJDBCPersisterCMPLijstpositiesBean extends EJSJDBCPersister implements com.logicacmg.koa.koaschema.EJSFinderLijstpositiesBean {
	/**
	 * @generated
	 */
	private static final String _createString = "INSERT INTO KOA01.LIJSTPOSITIES (POSITIENUMMER, KIESKRINGNUMMER, KIESLIJSTNUMMER, ACHTERNAAM, VOORLETTERS, ROEPNAAM, GESLACHT, WOONPLAATS) VALUES (?, ?, ?, ?, ?, ?, ?, ?)";
	/**
	 * @generated
	 */
	private static final String _removeString = "DELETE FROM KOA01.LIJSTPOSITIES  WHERE POSITIENUMMER = ? AND KIESKRINGNUMMER = ? AND KIESLIJSTNUMMER = ?";
	/**
	 * @generated
	 */
	private static final String _storeString = "UPDATE KOA01.LIJSTPOSITIES  SET ACHTERNAAM = ?, VOORLETTERS = ?, ROEPNAAM = ?, GESLACHT = ?, WOONPLAATS = ? WHERE POSITIENUMMER = ? AND KIESKRINGNUMMER = ? AND KIESLIJSTNUMMER = ?";
	/**
	 * @generated
	 */
	private static final String _loadString = "SELECT T1.POSITIENUMMER, T1.ACHTERNAAM, T1.VOORLETTERS, T1.ROEPNAAM, T1.GESLACHT, T1.WOONPLAATS, T1.KIESKRINGNUMMER, T1.KIESLIJSTNUMMER FROM KOA01.LIJSTPOSITIES  T1 WHERE T1.POSITIENUMMER = ? AND T1.KIESKRINGNUMMER = ? AND T1.KIESLIJSTNUMMER = ?";
	/**
	 * @generated
	 */
	private static final String _loadForUpdateString = _loadString + " FOR UPDATE";
	/**
	 * @generated
	 */
	private byte[] serObj = null;
	/**
	 * EJSJDBCPersisterCMPLijstpositiesBean
	 * @generated
	 */
	public EJSJDBCPersisterCMPLijstpositiesBean() throws java.rmi.RemoteException {
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
		LijstpositiesBean b = (LijstpositiesBean) eb;
		PreparedStatement pstmt;
		pstmt = getPreparedStatement(_createString);
		try {
			if (b.positienummer == null) {
				pstmt.setNull(1, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(1, b.positienummer);
			}
			if (b.achternaam == null) {
				pstmt.setNull(4, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(4, b.achternaam);
			}
			if (b.voorletters == null) {
				pstmt.setNull(5, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(5, b.voorletters);
			}
			if (b.roepnaam == null) {
				pstmt.setNull(6, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(6, b.roepnaam);
			}
			objectTemp = com.ibm.vap.converters.VapStringToCharacterConverter.singleton().dataFrom(new Character(b.geslacht));
			if (objectTemp == null) {
				pstmt.setNull(7, java.sql.Types.CHAR);
			}
			else {
				pstmt.setString(7, (java.lang.String)objectTemp);
			}
			if (b.woonplaats == null) {
				pstmt.setNull(8, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(8, b.woonplaats);
			}
			if (b.fk_klkr_1_kieslijstnummer == null) {
				pstmt.setNull(3, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(3, b.fk_klkr_1_kieslijstnummer);
			}
			if (b.fk_klkr_1_fk_kkr_1_kieskringnummer == null) {
				pstmt.setNull(2, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(2, b.fk_klkr_1_fk_kkr_1_kieskringnummer);
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
		LijstpositiesBean b = (LijstpositiesBean) eb;
		com.logicacmg.koa.koaschema.LijstpositiesKey _primaryKey = (com.logicacmg.koa.koaschema.LijstpositiesKey)pKey;
		java.sql.ResultSet resultSet = (java.sql.ResultSet) data;
		b.positienummer = _primaryKey.positienummer;
		b.fk_klkr_1_kieslijstnummer = _primaryKey.fk_klkr_1_kieslijstnummer;
		b.fk_klkr_1_fk_kkr_1_kieskringnummer = _primaryKey.fk_klkr_1_fk_kkr_1_kieskringnummer;
		b.achternaam = resultSet.getString(2);
		b.voorletters = resultSet.getString(3);
		b.roepnaam = resultSet.getString(4);
		objectTemp = com.ibm.vap.converters.VapStringToCharacterConverter.singleton().objectFrom(resultSet.getString(5));
		b.geslacht = (objectTemp == null) ? '\u0000' : ((Character)objectTemp).charValue();
		b.woonplaats = resultSet.getString(6);
		b.fk_klkr_1_kieslijstnummer = resultSet.getString(8);
		b.fk_klkr_1_fk_kkr_1_kieskringnummer = resultSet.getString(7);
	}
	/**
	 * load
	 * @generated
	 */
	public void load(EntityBean eb, Object pKey, boolean forUpdate) throws Exception {
		Object objectTemp = null;
		LijstpositiesBean b = (LijstpositiesBean) eb;
		com.logicacmg.koa.koaschema.LijstpositiesKey _primaryKey = (com.logicacmg.koa.koaschema.LijstpositiesKey)pKey;
		PreparedStatement pstmt;
		ResultSet resultSet = null;
		pstmt = (forUpdate) ?
			getPreparedStatement(_loadForUpdateString):
			getPreparedStatement(_loadString);
		try {
			if (_primaryKey.positienummer == null) {
				pstmt.setNull(1, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(1, _primaryKey.positienummer);
			}
			if (_primaryKey.fk_klkr_1_kieslijstnummer == null) {
				pstmt.setNull(3, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(3, _primaryKey.fk_klkr_1_kieslijstnummer);
			}
			if (_primaryKey.fk_klkr_1_fk_kkr_1_kieskringnummer == null) {
				pstmt.setNull(2, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(2, _primaryKey.fk_klkr_1_fk_kkr_1_kieskringnummer);
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
		LijstpositiesBean b = (LijstpositiesBean) eb;
		com.logicacmg.koa.koaschema.LijstpositiesKey _primaryKey = new com.logicacmg.koa.koaschema.LijstpositiesKey();
		_primaryKey.positienummer = b.positienummer;
		_primaryKey.fk_klkr_1_kieslijstnummer = b.fk_klkr_1_kieslijstnummer;
		_primaryKey.fk_klkr_1_fk_kkr_1_kieskringnummer = b.fk_klkr_1_fk_kkr_1_kieskringnummer;
		load(b, _primaryKey, forUpdate);
	}
	/**
	 * store
	 * @generated
	 */
	public void store(EntityBean eb) throws Exception {
		Object objectTemp = null;
		LijstpositiesBean b = (LijstpositiesBean) eb;
		com.logicacmg.koa.koaschema.LijstpositiesKey _primaryKey = new com.logicacmg.koa.koaschema.LijstpositiesKey();
		_primaryKey.positienummer = b.positienummer;
		_primaryKey.fk_klkr_1_kieslijstnummer = b.fk_klkr_1_kieslijstnummer;
		_primaryKey.fk_klkr_1_fk_kkr_1_kieskringnummer = b.fk_klkr_1_fk_kkr_1_kieskringnummer;
		PreparedStatement pstmt;
		pstmt = getPreparedStatement(_storeString);
		try {
			if (_primaryKey.positienummer == null) {
				pstmt.setNull(6, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(6, _primaryKey.positienummer);
			}
			if (_primaryKey.fk_klkr_1_kieslijstnummer == null) {
				pstmt.setNull(8, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(8, _primaryKey.fk_klkr_1_kieslijstnummer);
			}
			if (_primaryKey.fk_klkr_1_fk_kkr_1_kieskringnummer == null) {
				pstmt.setNull(7, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(7, _primaryKey.fk_klkr_1_fk_kkr_1_kieskringnummer);
			}
			if (b.achternaam == null) {
				pstmt.setNull(1, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(1, b.achternaam);
			}
			if (b.voorletters == null) {
				pstmt.setNull(2, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(2, b.voorletters);
			}
			if (b.roepnaam == null) {
				pstmt.setNull(3, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(3, b.roepnaam);
			}
			objectTemp = com.ibm.vap.converters.VapStringToCharacterConverter.singleton().dataFrom(new Character(b.geslacht));
			if (objectTemp == null) {
				pstmt.setNull(4, java.sql.Types.CHAR);
			}
			else {
				pstmt.setString(4, (java.lang.String)objectTemp);
			}
			if (b.woonplaats == null) {
				pstmt.setNull(5, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(5, b.woonplaats);
			}
			if (b.fk_klkr_1_kieslijstnummer == null) {
				pstmt.setNull(8, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(8, b.fk_klkr_1_kieslijstnummer);
			}
			if (b.fk_klkr_1_fk_kkr_1_kieskringnummer == null) {
				pstmt.setNull(7, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(7, b.fk_klkr_1_fk_kkr_1_kieskringnummer);
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
		LijstpositiesBean b = (LijstpositiesBean) eb;
		com.logicacmg.koa.koaschema.LijstpositiesKey _primaryKey = new com.logicacmg.koa.koaschema.LijstpositiesKey();
		_primaryKey.positienummer = b.positienummer;
		_primaryKey.fk_klkr_1_kieslijstnummer = b.fk_klkr_1_kieslijstnummer;
		_primaryKey.fk_klkr_1_fk_kkr_1_kieskringnummer = b.fk_klkr_1_fk_kkr_1_kieskringnummer;
		PreparedStatement pstmt;
		pstmt = getPreparedStatement(_removeString);
		try {
			if (_primaryKey.positienummer == null) {
				pstmt.setNull(1, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(1, _primaryKey.positienummer);
			}
			if (_primaryKey.fk_klkr_1_kieslijstnummer == null) {
				pstmt.setNull(3, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(3, _primaryKey.fk_klkr_1_kieslijstnummer);
			}
			if (_primaryKey.fk_klkr_1_fk_kkr_1_kieskringnummer == null) {
				pstmt.setNull(2, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(2, _primaryKey.fk_klkr_1_fk_kkr_1_kieskringnummer);
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
		com.logicacmg.koa.koaschema.LijstpositiesKey key = new com.logicacmg.koa.koaschema.LijstpositiesKey();
		java.sql.ResultSet resultSet = (java.sql.ResultSet) data;

		if (resultSet != null) {
			Object objectTemp = null;
			key.positienummer = resultSet.getString(1);
			key.fk_klkr_1_kieslijstnummer = resultSet.getString(8);
			key.fk_klkr_1_fk_kkr_1_kieskringnummer = resultSet.getString(7);
			return key;
		}
		return null;
	}
	/**
	 * findByPrimaryKey
	 * @generated
	 */
	public com.logicacmg.koa.koaschema.Lijstposities findByPrimaryKey(com.logicacmg.koa.koaschema.LijstpositiesKey primaryKey) throws java.rmi.RemoteException, javax.ejb.FinderException {
		return (com.logicacmg.koa.koaschema.Lijstposities) home.activateBean(primaryKey);
	}
	/**
	 * findLijstpositiesByFk_klkr_1
	 * @generated
	 */
	public EJSFinder findLijstpositiesByFk_klkr_1(com.logicacmg.koa.koaschema.KieslijstenKey inKey) throws javax.ejb.FinderException, java.rmi.RemoteException {
		ResultSet resultSet = null;
		PreparedStatement pstmt = null;
		try {
			preFind();
			pstmt = getPreparedStatement("SELECT T1.POSITIENUMMER, T1.ACHTERNAAM, T1.VOORLETTERS, T1.ROEPNAAM, T1.GESLACHT, T1.WOONPLAATS, T1.KIESKRINGNUMMER, T1.KIESLIJSTNUMMER FROM KOA01.LIJSTPOSITIES  T1 WHERE T1.KIESKRINGNUMMER = ? AND T1.KIESLIJSTNUMMER = ?");
			Object objectTemp = null;
			boolean nullData;
			if (inKey.kieslijstnummer == null) {
				pstmt.setNull(2, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(2, inKey.kieslijstnummer);
			}
			if (inKey.fk_kkr_1_kieskringnummer == null) {
				pstmt.setNull(1, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(1, inKey.fk_kkr_1_kieskringnummer);
			}
			resultSet = pstmt.executeQuery();
			return new EJSJDBCFinder(resultSet, this, pstmt);
		}
		catch (Exception ex) {
			throw new EJSPersistenceException("find failed:", ex);
		}
	}
}
