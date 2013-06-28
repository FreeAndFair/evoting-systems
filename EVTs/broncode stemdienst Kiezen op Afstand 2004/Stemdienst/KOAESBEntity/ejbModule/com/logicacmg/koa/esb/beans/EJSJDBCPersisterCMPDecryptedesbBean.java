package com.logicacmg.koa.esb.beans;
import com.ibm.ejs.persistence.*;
import javax.ejb.EntityBean;
import java.sql.*;
import java.text.*;
import com.ibm.vap.converters.*;
import com.ibm.vap.converters.streams.*;
/**
 * EJSJDBCPersisterCMPDecryptedesbBean
 * @generated
 */
public class EJSJDBCPersisterCMPDecryptedesbBean extends EJSJDBCPersister implements com.logicacmg.koa.esb.beans.EJSFinderDecryptedesbBean {
	/**
	 * @generated
	 */
	private static final String _createString = "INSERT INTO KOA01.DECRYPTEDESB (STEMNUMMER, KANDIDAATCODE, KIESKRINGNUMMER, DISTRICTNUMMER, KIESLIJSTNUMMER, POSITIENUMMER, LIJSTNAAM, ACHTERNAAM, VOORLETTERS) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)";
	/**
	 * @generated
	 */
	private static final String _removeString = "DELETE FROM KOA01.DECRYPTEDESB  WHERE STEMNUMMER = ?";
	/**
	 * @generated
	 */
	private static final String _storeString = "UPDATE KOA01.DECRYPTEDESB  SET KANDIDAATCODE = ?, KIESKRINGNUMMER = ?, DISTRICTNUMMER = ?, KIESLIJSTNUMMER = ?, POSITIENUMMER = ?, LIJSTNAAM = ?, ACHTERNAAM = ?, VOORLETTERS = ? WHERE STEMNUMMER = ?";
	/**
	 * @generated
	 */
	private static final String _loadString = "SELECT T1.STEMNUMMER, T1.KANDIDAATCODE, T1.KIESKRINGNUMMER, T1.DISTRICTNUMMER, T1.KIESLIJSTNUMMER, T1.POSITIENUMMER, T1.LIJSTNAAM, T1.ACHTERNAAM, T1.VOORLETTERS FROM KOA01.DECRYPTEDESB  T1 WHERE T1.STEMNUMMER = ?";
	/**
	 * @generated
	 */
	private static final String _loadForUpdateString = _loadString + " FOR UPDATE";
	/**
	 * @generated
	 */
	private byte[] serObj = null;
	/**
	 * EJSJDBCPersisterCMPDecryptedesbBean
	 * @generated
	 */
	public EJSJDBCPersisterCMPDecryptedesbBean() throws java.rmi.RemoteException {
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
		DecryptedesbBean b = (DecryptedesbBean) eb;
		PreparedStatement pstmt;
		pstmt = getPreparedStatement(_createString);
		try {
			if (b.stemnummer == null) {
				pstmt.setNull(1, java.sql.Types.DECIMAL);
			}
			else {
				pstmt.setBigDecimal(1, b.stemnummer);
			}
			if (b.kandidaatcode == null) {
				pstmt.setNull(2, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(2, b.kandidaatcode);
			}
			if (b.kieskringnummer == null) {
				pstmt.setNull(3, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(3, b.kieskringnummer);
			}
			if (b.districtnummer == null) {
				pstmt.setNull(4, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(4, b.districtnummer);
			}
			if (b.kieslijstnummer == null) {
				pstmt.setNull(5, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(5, b.kieslijstnummer);
			}
			if (b.positienummer == null) {
				pstmt.setNull(6, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(6, b.positienummer);
			}
			if (b.lijstnaam == null) {
				pstmt.setNull(7, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(7, b.lijstnaam);
			}
			if (b.achternaam == null) {
				pstmt.setNull(8, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(8, b.achternaam);
			}
			if (b.voorletters == null) {
				pstmt.setNull(9, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(9, b.voorletters);
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
		DecryptedesbBean b = (DecryptedesbBean) eb;
		com.logicacmg.koa.esb.beans.DecryptedesbKey _primaryKey = (com.logicacmg.koa.esb.beans.DecryptedesbKey)pKey;
		java.sql.ResultSet resultSet = (java.sql.ResultSet) data;
		b.stemnummer = _primaryKey.stemnummer;
		b.kandidaatcode = resultSet.getString(2);
		b.kieskringnummer = resultSet.getString(3);
		b.districtnummer = resultSet.getString(4);
		b.kieslijstnummer = resultSet.getString(5);
		b.positienummer = resultSet.getString(6);
		b.lijstnaam = resultSet.getString(7);
		b.achternaam = resultSet.getString(8);
		b.voorletters = resultSet.getString(9);
	}
	/**
	 * load
	 * @generated
	 */
	public void load(EntityBean eb, Object pKey, boolean forUpdate) throws Exception {
		Object objectTemp = null;
		DecryptedesbBean b = (DecryptedesbBean) eb;
		com.logicacmg.koa.esb.beans.DecryptedesbKey _primaryKey = (com.logicacmg.koa.esb.beans.DecryptedesbKey)pKey;
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
		DecryptedesbBean b = (DecryptedesbBean) eb;
		com.logicacmg.koa.esb.beans.DecryptedesbKey _primaryKey = new com.logicacmg.koa.esb.beans.DecryptedesbKey();
		_primaryKey.stemnummer = b.stemnummer;
		load(b, _primaryKey, forUpdate);
	}
	/**
	 * store
	 * @generated
	 */
	public void store(EntityBean eb) throws Exception {
		Object objectTemp = null;
		DecryptedesbBean b = (DecryptedesbBean) eb;
		com.logicacmg.koa.esb.beans.DecryptedesbKey _primaryKey = new com.logicacmg.koa.esb.beans.DecryptedesbKey();
		_primaryKey.stemnummer = b.stemnummer;
		PreparedStatement pstmt;
		pstmt = getPreparedStatement(_storeString);
		try {
			if (_primaryKey.stemnummer == null) {
				pstmt.setNull(9, java.sql.Types.DECIMAL);
			}
			else {
				pstmt.setBigDecimal(9, _primaryKey.stemnummer);
			}
			if (b.kandidaatcode == null) {
				pstmt.setNull(1, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(1, b.kandidaatcode);
			}
			if (b.kieskringnummer == null) {
				pstmt.setNull(2, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(2, b.kieskringnummer);
			}
			if (b.districtnummer == null) {
				pstmt.setNull(3, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(3, b.districtnummer);
			}
			if (b.kieslijstnummer == null) {
				pstmt.setNull(4, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(4, b.kieslijstnummer);
			}
			if (b.positienummer == null) {
				pstmt.setNull(5, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(5, b.positienummer);
			}
			if (b.lijstnaam == null) {
				pstmt.setNull(6, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(6, b.lijstnaam);
			}
			if (b.achternaam == null) {
				pstmt.setNull(7, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(7, b.achternaam);
			}
			if (b.voorletters == null) {
				pstmt.setNull(8, java.sql.Types.VARCHAR);
			}
			else {
				pstmt.setString(8, b.voorletters);
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
		DecryptedesbBean b = (DecryptedesbBean) eb;
		com.logicacmg.koa.esb.beans.DecryptedesbKey _primaryKey = new com.logicacmg.koa.esb.beans.DecryptedesbKey();
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
		com.logicacmg.koa.esb.beans.DecryptedesbKey key = new com.logicacmg.koa.esb.beans.DecryptedesbKey();
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
	public com.logicacmg.koa.esb.beans.Decryptedesb findByPrimaryKey(com.logicacmg.koa.esb.beans.DecryptedesbKey primaryKey) throws java.rmi.RemoteException, javax.ejb.FinderException {
		return (com.logicacmg.koa.esb.beans.Decryptedesb) home.activateBean(primaryKey);
	}
	/**
	 * findByLijstpositie
	 * @generated
	 */
	public com.logicacmg.koa.esb.beans.Decryptedesb findByLijstpositie(java.lang.String sKieskringnummer, java.lang.String sKieslijstnummer, java.lang.String sPositienummer) throws javax.ejb.FinderException, java.rmi.RemoteException {
		ResultSet resultSet = null;
		PreparedStatement pstmt = null;
		com.logicacmg.koa.esb.beans.Decryptedesb result = null;

		EJSJDBCFinder tmpFinder = null;
		try {
			preFind();
			pstmt = getPreparedStatement("SELECT T1.STEMNUMMER, T1.KANDIDAATCODE, T1.KIESKRINGNUMMER, T1.DISTRICTNUMMER, T1.KIESLIJSTNUMMER, T1.POSITIENUMMER, T1.LIJSTNAAM, T1.ACHTERNAAM, T1.VOORLETTERS FROM KOA01.DECRYPTEDESB  T1 WHERE kieskringnummer = ? AND kieslijstnummer = ? AND positienummer = ? FETCH FIRST 1 ROWS ONLY");
			if (sKieskringnummer == null) {
			   pstmt.setNull(1, java.sql.Types.VARCHAR);
			} else {
			   pstmt.setString(1, sKieskringnummer);
			}
			if (sKieslijstnummer == null) {
			   pstmt.setNull(2, java.sql.Types.VARCHAR);
			} else {
			   pstmt.setString(2, sKieslijstnummer);
			}
			if (sPositienummer == null) {
			   pstmt.setNull(3, java.sql.Types.VARCHAR);
			} else {
			   pstmt.setString(3, sPositienummer);
			}
			resultSet = pstmt.executeQuery();
			tmpFinder = new EJSJDBCFinder(resultSet, this, pstmt);
			if (tmpFinder.hasMoreElements()) {
				result = (com.logicacmg.koa.esb.beans.Decryptedesb)tmpFinder.nextElement();
			}
		}
		catch (Exception ex) {
			throw new EJSPersistenceException("find failed:", ex);
		}
		finally {
			if ( tmpFinder != null ) tmpFinder.close();
		}
		if (result == null) {
			throw new javax.ejb.ObjectNotFoundException();
		}
		return result;
	}
}
