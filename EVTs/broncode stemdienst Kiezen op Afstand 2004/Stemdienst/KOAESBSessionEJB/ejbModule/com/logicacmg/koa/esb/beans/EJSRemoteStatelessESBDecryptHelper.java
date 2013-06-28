package com.logicacmg.koa.esb.beans;
import com.ibm.ejs.container.*;
import javax.ejb.*;
import java.rmi.RemoteException;
/**
 * EJSRemoteStatelessESBDecryptHelper
 * @generated
 */
public class EJSRemoteStatelessESBDecryptHelper extends EJSWrapper implements ESBDecryptHelper {
	/**
	 * EJSRemoteStatelessESBDecryptHelper
	 * @generated
	 */
	public EJSRemoteStatelessESBDecryptHelper() throws java.rmi.RemoteException {
		super();	}
	/**
	 * saveDecryptedVotes
	 * @generated
	 */
	public int saveDecryptedVotes(java.util.Vector decryptedVotes, int stemnummerCount) throws com.logicacmg.koa.exception.KOAException, java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		int _EJS_result = 0;
		try {
			com.logicacmg.koa.esb.beans.ESBDecryptHelperBean beanRef = (com.logicacmg.koa.esb.beans.ESBDecryptHelperBean)container.preInvoke(this, 0, _EJS_s);
			_EJS_result = beanRef.saveDecryptedVotes(decryptedVotes, stemnummerCount);
		}
		catch (com.logicacmg.koa.exception.KOAException ex) {
			_EJS_s.setCheckedException(ex);
			throw ex;
		}
		catch (java.rmi.RemoteException ex) {
			_EJS_s.setUncheckedException(ex);
		}
		catch (Throwable ex) {
			_EJS_s.setUncheckedException(ex);
			throw new RemoteException("bean method raised unchecked exception", ex);
		}

		finally {
			container.postInvoke(this, 0, _EJS_s);
		}
		return _EJS_result;
	}
}
