package edu.uconn.cse.adder.plugin;

import java.applet.Applet;
import java.security.AccessController;
import java.security.PrivilegedAction;
import java.security.PrivilegedActionException;
import java.security.PrivilegedExceptionAction;

import edu.uconn.cse.adder.InvalidPublicKeyException;
import edu.uconn.cse.adder.InvalidVoteException;

/**
 * The adder applet.
 *
 * @author David Walluck
 * @version $LastChangedRevision$ $LastChangedDate$
 * @since 0.0.1
 */
public class AdderApplet extends Applet {
    private static final long serialVersionUID = 0L;
    private static final String LIBADDER_VERSION = "0.0.1";

    /**
     * Initializes the applet.
     *
     * @see java.applet.Applet#init()
     */
    public void init() {
        String plibadderVersion = getParameter("libadder-version");

        if (plibadderVersion == null
            || !plibadderVersion.equals(LIBADDER_VERSION)) {
            throw new RuntimeException("incorrect version: expected: "
                                       + LIBADDER_VERSION + ", was: "
                                       + plibadderVersion);
        }
    }

    /**
     * Gets the applet information.
     *
     * @see java.applet.Applet#getAppletInfo()
     * @return the applet information
     */
    public String getAppletInfo() {
        return "Title: Adder for Java\n"
            + "Author: David Walluck\n"
            + "Adder Java applet.";
    }

    /**
     * Gets the applet parameter information.
     *
     * @see java.applet.Applet#getParameterInfo()
     * @return the parameter information
     */
    public String[][] getParameterInfo() {
        final String[][] pinfo = {
            {"version", "string", "libadder version string"}
        };

        return pinfo;
    }

    /**
     * Encrypts a vote.
     *
     * @param key the key
     * @param vote the vote
     * @param min the minimum number of allowed choices
     * @param max the maximum number of allowed choices
     * @return the encrypted vote
     */
    public String encryptVote(final String key, final String vote,
                              final int min, final int max) {
        try {
            String ret = (String) AccessController.
            doPrivileged(new PrivilegedExceptionAction/*<String>*/() {
                public /*String*/Object run() {
                    return Plugin.encryptVote(key, vote, min, max);
                }
            });

            return ret;
        } catch (PrivilegedActionException e) {
            throw (InvalidPublicKeyException) e.getException();
        }
    }

    /**
     * Creates a key pair.
     *
     * @param user the user
     * @param procedure the procedure
     * @param key the key
     * @param secure true if secure
     * @return true if the keypair was created successfully
     */
    public boolean createKeyPair(final String user, final String procedure,
                                 final String key, final boolean secure) {
        try {
            Boolean ret = (Boolean) AccessController.
            doPrivileged(new PrivilegedExceptionAction/*<Boolean>*/() {
                public /*Boolean*/Object run() {
                    return Boolean.valueOf(Plugin.createKeyPair(user,
                                                                procedure,
                                                                key,
                                                                secure));
                }
            });

            return ret.booleanValue();
        } catch (PrivilegedActionException e) {
            throw (InvalidPublicKeyException) e.getException();
        }
    }

    /**
     * Decrypts the final vote.
     *
     * @param user the user
     * @param procedure the procedure
     * @param voteString the vote string
     * @return the decrypted sum
     */
    public String decryptSum(final String user, final String procedure,
                             final String voteString) {
        try {
            String ret = (String) AccessController.
            doPrivileged(new PrivilegedExceptionAction/*<String>*/() {
                public /*String*/Object run() {
                    return Plugin.decryptSum(user, procedure, voteString);
                }
            });

            return ret;
        } catch (PrivilegedActionException e) {
            throw (InvalidVoteException) e.getException();
        }
    }

    /**
     * Reads the public key.
     *
     * @param user the user
     * @param procedure the procedure
     * @return the public key
     */
    public String readPubKey(final String user, final String procedure) {
        try {
            String ret = (String) AccessController.
            doPrivileged(new PrivilegedExceptionAction/*<String>*/() {
                public /*String*/Object run() {
                    return Plugin.readPubKey(user, procedure);
                }
            });

            return ret;
        } catch (PrivilegedActionException e) {
            throw (InvalidPublicKeyException) e.getException();
        }
    }

    /**
     * Reads the private key.
     *
     * @param user the user
     * @param procedure the procedure
     * @return the private key
     */
    public String readPrivKey(final String user, final String procedure) {
        String ret = (String) AccessController.
        doPrivileged(new PrivilegedAction/*<String>*/() {
            public /*String*/Object run() {
                return Plugin.readPrivKey(user, procedure);
            }
        });

        return ret;
    }

    /**
     * Writes the private key.
     *
     * @param user the user
     * @param procedure the procedure
     * @param key the private key
     * @return true of the private key was written successfully
     */
    public boolean writePrivKey(final String user, final String procedure,
                                final String key) {
        Boolean ret = (Boolean) AccessController.
        doPrivileged(new PrivilegedAction/*<Boolean>*/() {
            public /*Boolean*/Object run() {
                return Boolean.valueOf(Plugin.writePrivKey(user, procedure,
                                                           key));
            }
        });

        return ret.booleanValue();
    }

    /**
     * Reads the second private key.
     *
     * @param user the user
     * @param procedure the procedure
     * @return the second private key
     */
    public String readPrivKey2(final String user, final String procedure) {
        String ret = (String) AccessController.
        doPrivileged(new PrivilegedAction/*<String>*/() {
            public /*String*/Object run() {
                return Plugin.readPrivKey2(user, procedure);
            }
        });

        return ret;
    }

    /**
     * Writes the second private key.
     *
     * @param user the user
     * @param procedure the procedure
     * @param key the second private key
     * @return true if the second private key was written successfully
     */
    public boolean writePrivKey2(final String user, final String procedure,
                                 final String key) {
        Boolean ret = (Boolean) AccessController.
        doPrivileged(new PrivilegedAction/*<Boolean>*/() {
            public /*Boolean*/Object run() {
                return Boolean.valueOf(Plugin.writePrivKey2(user, procedure,
                                                            key));
            }
        });

        return ret.booleanValue();
    }

    /**
     * Computes the secret key.
     *
     * @param user the user
     * @param procedure the procedure
     * @param keys the keys
     * @return true if the key was computed successfully
     */
    public boolean computeSecretKey(final String user, final String procedure,
                                    final String keys) {
        try {
            Boolean ret = (Boolean) AccessController.
            doPrivileged(new PrivilegedExceptionAction/*<Boolean>*/() {
                public /*Boolean*/Object run() {
                    return Boolean.valueOf(Plugin.computeSecretKey(user,
                                                                   procedure,
                                                                   keys));
                }
            });

            return ret.booleanValue();
        } catch (PrivilegedActionException e) {
            throw (RuntimeException) e.getException();
        }
    }

    /**
     * Encrypts the polynomial.
     *
     * @param user the user
     * @param procedure the procedure
     * @param keys the keys
     * @param degree the degree of the polynomial
     * @return the encrypted polynomial
     */
    public String encryptPoly(final String user, final String procedure,
                              final String keys, final int degree) {
        try {
            String ret = (String) AccessController.
            doPrivileged(new PrivilegedExceptionAction/*<String>*/() {
                public /*String*/Object run() {
                    return Plugin.encryptPoly(user, procedure, keys, degree);
                }
            });

            return ret;
        } catch (PrivilegedActionException e) {
            throw (InvalidPublicKeyException) e.getException();
        }
    }

    /**
     * Encrypts the <code>g</code> value.
     *
     * @param user the user
     * @param procedure the procedure
     * @return the <code>g</code> value
     */
    public String encryptGValue(final String user, final String procedure) {
        String ret = (String) AccessController.
        doPrivileged(new PrivilegedAction/*<String>*/() {
            public /*String*/Object run() {
                return Plugin.encryptGValue(user, procedure);
            }
        });

        return ret;
    }

    /**
     * Calculates the short hash of the given vote.
     *
     * @param voteString the vote string
     * @return the short hash
     */
    public String shortHash(final String voteString) {
        try {
            String ret = (String) AccessController.
            doPrivileged(new PrivilegedExceptionAction/*<String>*/() {
                public /*String*/Object run() {
                    return Plugin.shortHash(voteString);
                }
            });

            return ret;
        } catch (PrivilegedActionException e) {
            throw (InvalidVoteException) e.getException();
        }
    }
}
