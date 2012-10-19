

package org.scantegrity.sws.stripes.ext;


import java.util.Locale;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpSession;

import net.sourceforge.stripes.config.Configuration;
import net.sourceforge.stripes.localization.DefaultLocalePicker;
 

public class LocaleManager extends DefaultLocalePicker {
    public static final String LOCALE = "locale";

    public void init(Configuration p_config) throws Exception {
    	super.init(p_config);

    	//What locales are supported?
    	
    	//Save supported locales
    	
    }
    
    @Override
    public Locale pickLocale(HttpServletRequest p_request) {
        HttpSession l_session = p_request.getSession();
        Locale l_res = null;
        
        //Is there a session set up for this user yet?
        String l_locale = (String) l_session.getAttribute(LOCALE);
        if (l_locale == null) {
        	//Create locale list based on user's Accept-Header and our supported
        	//language list.
        	
        	l_res = super.pickLocale(p_request);
        } else {
        	l_res = new Locale(l_locale);
        }
        
        //Change the locale if requested
    	String l_tmp = p_request.getParameter(LOCALE);
        if (l_tmp != null) {
            l_session.setAttribute(LOCALE, l_tmp);
            l_res = new Locale(l_tmp);
        }

        return l_res;
    }
}

