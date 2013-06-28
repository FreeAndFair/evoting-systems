package com.logicacmg.koa.esb.beans;
import com.ibm.ejs.container.*;
import javax.ejb.*;
import java.rmi.RemoteException;
/**
 * EJSRemoteCMPEncryptedesb
 * @generated
 */
public class EJSRemoteCMPEncryptedesb extends EJSWrapper implements Encryptedesb {
	/**
	 * EJSRemoteCMPEncryptedesb
	 * @generated
	 */
	public EJSRemoteCMPEncryptedesb() throws java.rmi.RemoteException {
		super();	}
	/**
	 * getStem
	 * @generated
	 */
	public byte[] getStem() throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		byte[] _EJS_result = null;
		try {
			com.logicacmg.koa.esb.beans.EncryptedesbBean beanRef = (com.logicacmg.koa.esb.beans.EncryptedesbBean)container.preInvoke(this, 0, _EJS_s);
			_EJS_result = beanRef.getStem();
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
	/**
	 * setStem
	 * @generated
	 */
	public void setStem(byte[] newStem) throws java.rmi.RemoteException {
		EJSDeployedSupport _EJS_s = new EJSDeployedSupport();
		
		try {
			com.logicacmg.koa.esb.beans.EncryptedesbBean beanRef = (com.logicacmg.koa.esb.beans.EncryptedesbBean)container.preInvoke(this, 1, _EJS_s);
			beanRef.setStem(newStem);
		}
		catch (java.rmi.RemoteException ex) {
			_EJS_s.setUncheckedException(ex);
		}
		catch (Throwable ex) {
			_EJS_s.setUncheckedException(ex);
			throw new RemoteException("bean method raised unchecked exception", ex);
		}

		finally {
			container.postInvoke(this, 1, _EJS_s);
		}
		return ;
	}
}
