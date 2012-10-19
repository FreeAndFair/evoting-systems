/**
 * 
 */

package org.scantegrity.sws.stripes.ext;

import java.util.List;

import net.sourceforge.stripes.action.ActionBean;
import net.sourceforge.stripes.controller.NameBasedActionResolver;


/**
 * Changes the default name resolver functionality. See:
 *	http://www.stripesframework.org/display/stripes/Use+Defaults+More
 * 
 * @author Rick Carback
 */
public class NameResolutionManager extends NameBasedActionResolver {

	//Lowercase looks nicer
	@Override
	protected String getUrlBinding(String p_actionBeanName) {
		return super.getUrlBinding(p_actionBeanName).toLowerCase();
	}
	
    //We don't care able suffixes
    @Override
    public String getBindingSuffix() { return ""; }
    
    /**
     * NOTE: Apparently Dynamic filter doesn't call the resolver, 
     * that's why the following is here, see:
     * 
     * http://sourceforge.net/mailarchive/message.php?msg_id=loom.20080824T181237-818%40post.gmane.org
     */
    @Override
    public Class<? extends ActionBean> getActionBeanType(String p_path) {
    	//System.err.println(p_path);
    	p_path = p_path.toLowerCase();
    	Class<? extends ActionBean> l_cls = super.getActionBeanType(p_path);
    	if (l_cls == null) {
			ActionBean l_bean = handleActionBeanNotFound(null, p_path);
			if (l_bean != null) {
				//l_bean = new DefaultActionBean(); 
				return l_bean.getClass();
			}
    	}
    	return l_cls;
    }
    
    //JSP is in protected folder (idea also taken from link above).
    @Override
    protected List<String> getFindViewAttempts(String p_url) {
    	List<String> l_view = super.getFindViewAttempts(p_url);
    	for (int l_i = 0; l_i < l_view.size(); l_i++) {
    		l_view.set(l_i, "/WEB-INF/pages" + l_view.get(l_i));
    	}
    	return l_view;
    }    
}
