/** -----------------------------------------------------------------------
  *
  *   DBRegistry.java
  *
  * -----------------------------------------------------------------------
  * 
  *  (c) 2003  Ministerie van Binnenlandse Zaken en Koninkrijkrelaties
  *
  *  Project		: Kiezen Op Afstand (KOA)
  *  Project Number	: ECF-2651
  *  
  *  History:
  *  Version	Date		Name		Reason
  * ---------------------------------------------------------
  *  0.1		29-05-2003	XUi			First implementation
  *
  * 
  * -----------------------------------------------------------------------
  */
import java.io.BufferedReader;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.security.cert.X509Certificate;
import java.sql.Connection;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;
import java.util.ArrayList;
import java.util.List;
import java.util.Properties;
import javax.naming.Context;
import javax.naming.InitialContext;
import javax.sql.DataSource;
import com.ibm.websphere.security.CertificateMapFailedException;
import com.ibm.websphere.security.CertificateMapNotSupportedException;
import com.ibm.websphere.security.CustomRegistry;
import com.ibm.websphere.security.CustomRegistryException;
import com.ibm.websphere.security.EntryNotFoundException;
import com.ibm.websphere.security.PasswordCheckFailedException;
import com.logicacmg.koa.exception.KOAException;
/**
 * Class implementing the custom registry interface to
 * handle the security authentication in WebSphere via
 * the custom registry option.
 * 
 * @author UiterliX
 * 
 */
public class DBRegistry implements CustomRegistry
{
	/**
	 * Private method to hash a password so the incoming password
	 * can be compared to the saved password.
	 * 
	 * @param password The password to hash
	 * 
	 * @return String the hashed password
	 * 
	 * @throws Exception A general exception when something goes wrong hashing the password.
	 * 
	 */
	private static String hashPassword(String password) throws Exception
	{
		MessageDigest md = null;
		try
		{
			md = MessageDigest.getInstance("SHA-1");
			md.update(password.getBytes());
		}
		catch (java.security.NoSuchAlgorithmException nse)
		{
			throw new Exception("ENC-01");
		}
		byte[] output = md.digest();
		StringBuffer sb = new StringBuffer(2 * output.length);
		for (int i = 0; i < output.length; ++i)
		{
			int k = output[i] & 0xFF;
			if (k < 0x10)
				sb.append('0');
			sb.append(Integer.toHexString(k));
		}
		return sb.toString();
	}
	/**
	 * Gets the connection to the database.
	 * Uses datasource with name 'jdbc/Registry'
	 * 
	 * @return Connection the connection to the database.
	 * 
	 * @throws Exception General exception when something goes wrong getting the connection.
	 * 
	 */
	private Connection getConnection() throws Exception
	{
		Connection conn = null;
		Context ctx = new InitialContext();
		DataSource datasource = (DataSource) ctx.lookup("jdbc/Registry");
		conn = datasource.getConnection();
		return conn;
	}
	/**
	 * Constructor for the db registry.
	 * 
	 */
	public DBRegistry()
	{
		System.out.println("[DBRegistry] Constructor");
	} // Default Constructor
	/**
	* Initializes the registry.
	* @param props the registry-specific properties with which to
	* initialize the registry object.
	* @exception CustomRegistryException if there is a problem.
	**/
	public void initialize(java.util.Properties props)
		throws CustomRegistryException
	{
		System.out.println("[DBRegistry] Initialize");
		Connection conn = null;
		try
		{
			conn = getConnection();
		}
		catch (Exception e)
		{
			throw new CustomRegistryException(e.getMessage());
		}
		finally
		{
			try
			{
				conn.close();
			}
			catch (Exception e)
			{
			}
		}
	}
	/**
	* Checks the Password of the user.
	* @param userId the user name data to authenticate.
	* @param passwd the password of the user.
	* @return the userId that will be used for authentication.
	* @exception WrongPasswordException if passwd is not valid.
	* @exception CustomRegistryException if there are any other problems.
	**/
	public String checkPassword(String userId, String passwd)
		throws PasswordCheckFailedException, CustomRegistryException
	{
		System.out.println("[DBRegistry] checkPassword user: " + userId);
		String userName = null;
		Connection conn = null;
		Statement stmt = null;
		ResultSet rst = null;
		try
		{
			String password = hashPassword(passwd);
			conn = getConnection();
			stmt = conn.createStatement();
			rst =
				stmt.executeQuery(
					"SELECT USER_ID FROM REGSCHEMA.USER WHERE USER_ID='"
						+ userId
						+ "' AND PASSWORD='"
						+ password
						+ "'");
			if (rst.next())
			{
				userName = userId;
			}
		}
		catch (Exception ex)
		{
			throw new CustomRegistryException(ex.getMessage());
		}
		finally
		{
			try
			{
				rst.close();
			}
			catch (SQLException sqle)
			{
			}
			try
			{
				stmt.close();
			}
			catch (SQLException sqle)
			{
			}
			try
			{
				conn.close();
			}
			catch (SQLException sqle)
			{
			}
		}
		if (userName == null)
		{
			throw new PasswordCheckFailedException(userId);
		}
		return userName;
	}
	/**
	* Maps a Certificate (of X509 format) to a valid userId in the Registry.
	* @param cert the certificate that needs to be mapped.
	* @return the mapped name of the user (userId).
	* @exception CertificateMapNotSupportedException if the particular
	* certificate is not supported.
	* @exception CertificateMapFailedException if the mapping of the
	* certificate fails.
	* @exception CustomRegistryException if there are any other problems.
	**/
	public String mapCertificate(X509Certificate cert)
		throws
			CertificateMapNotSupportedException,
			CertificateMapFailedException,
			CustomRegistryException
	{
		System.out.println("[DBRegistry] mapCertificate");
		String name = null;
		try
		{
			// map the SubjectDN in the certificate to a userID.
			name = cert.getSubjectDN().getName();
		}
		catch (Exception ex)
		{
			throw new CertificateMapNotSupportedException(ex.getMessage());
		}
		if (!isValidUser(name))
		{
			throw new CertificateMapFailedException(name);
		}
		return name;
	}
	/**
	* Returns the realm of the registry.
	* @return the realm. The realm is a registry-specific string indicating the
	* realm or domain for which this registry applies.  For example, for
	* OS400 or AIX,  this would be the host name of the system whose user registry
	* this object represents.
	* If null is returned by this method, realm defaults to the value of
	* "customRealm".
	* @exception CustomRegistryException if there are any other problems.
	**/
	public String getRealm() throws CustomRegistryException
	{
		System.out.println("[DBRegistry] getRealm");
		String name = "koabuild";
		return name;
	}
	/**
	* Returns the names of all  users in the registry.
	* @return a List of the names of all the users.
	* @exception CustomRegistryException if there are any other problems.
	**/
	public List getUsers() throws CustomRegistryException
	{
		System.out.println("[DBRegistry] getUsers");
		BufferedReader in = null;
		List allUsers = new ArrayList();
		Connection conn = null;
		Statement stmt = null;
		ResultSet rst = null;
		try
		{
			conn = getConnection();
			stmt = conn.createStatement();
			rst = stmt.executeQuery("SELECT USER_ID FROM REGSCHEMA.USER");
			while (rst.next())
			{
				allUsers.add(rst.getString("USER_ID"));
			}
		}
		catch (Exception ex)
		{
			throw new CustomRegistryException(ex.getMessage());
		}
		finally
		{
			try
			{
				rst.close();
			}
			catch (SQLException sqle)
			{
			}
			try
			{
				stmt.close();
			}
			catch (SQLException sqle)
			{
			}
			try
			{
				conn.close();
			}
			catch (SQLException sqle)
			{
			}
		}
		return allUsers;
	}
	/**
	* Returns names of the users in the registry that match a pattern.
	* @param pattern the pattern to match (for example, a* will match all
	* userNames starting with a). At a minimum when a full name is used
	* as the pattern, the full name should be returned  if it is a
	* valid user.
	* @return a List of the names of all  users that match the pattern.
	* @exception CustomRegistryException if there are any other problems.
	**/
	public List getUsers(String pattern) throws CustomRegistryException
	{
		System.out.println("[DBRegistry] getUsers pattern: " + pattern);
		BufferedReader in = null;
		List allUsers = new ArrayList();
		Connection conn = null;
		Statement stmt = null;
		ResultSet rst = null;
		try
		{
			conn = getConnection();
			stmt = conn.createStatement();
			rst = stmt.executeQuery("SELECT USER_ID FROM REGSCHEMA.USER");
			while (rst.next())
			{
				allUsers.add(rst.getString("USER_ID"));
			}
		}
		catch (Exception ex)
		{
			throw new CustomRegistryException(ex.getMessage());
		}
		finally
		{
			try
			{
				rst.close();
			}
			catch (SQLException sqle)
			{
			}
			try
			{
				stmt.close();
			}
			catch (SQLException sqle)
			{
			}
			try
			{
				conn.close();
			}
			catch (SQLException sqle)
			{
			}
		}
		return allUsers;
	}
	/**
	* Returns the names of all the users in a group.
	* @param groupName the name of the group.
	* @return a List of all the names of the users in the group.
	* @exception EntryNotFoundException if groupName does not exist.
	* @exception CustomRegistryException if there are any other problems.
	**/
	public List getUsersForGroup(String groupName)
		throws CustomRegistryException, EntryNotFoundException
	{
		System.out.println("[DBRegistry] getUsersForGroup: " + groupName);
		List usrsForGroup = new ArrayList();
		Connection conn = null;
		Statement stmt = null;
		ResultSet rst = null;
		try
		{
			conn = getConnection();
			stmt = conn.createStatement();
			rst =
				stmt.executeQuery(
					"SELECT USER_ID FROM REGSCHEMA.USER_GROUP WHERE GROUP_ID='"
						+ groupName
						+ "'");
			while (rst.next())
			{
				usrsForGroup.add(rst.getString("USER_ID"));
			}
		}
		catch (Exception ex)
		{
			if (!isValidGroup(groupName))
			{
				throw new EntryNotFoundException(groupName);
			}
			throw new CustomRegistryException(ex.getMessage());
		}
		finally
		{
			try
			{
				rst.close();
			}
			catch (SQLException sqle)
			{
			}
			try
			{
				stmt.close();
			}
			catch (SQLException sqle)
			{
			}
			try
			{
				conn.close();
			}
			catch (SQLException sqle)
			{
			}
		}
		return usrsForGroup;
	}
	/**
	* Returns the display name for the user specified by userName.
	* @param userName the name of the user.
	* @return the display name for the user. The display name
	* is a registry-specific string that represents a descriptive, not
	* necessarily a unique, name for a user. If a display name does not exist,
	* return null.
	* @exception EntryNotFoundException if userName does not exist.
	* @exception CustomRegistryException if there are any other problems.
	**/
	public String getUserDisplayName(String userName)
		throws CustomRegistryException, EntryNotFoundException
	{
		System.out.println("[DBRegistry] getUserDisplayName: " + userName);
		return userName;
	}
	/**
	* Returns the UniqueId for a userName.
	* @param userName the name of the user.
	* @return the UniqueId of the user. The UniqueId for an user is
	* the stringified form of some unique, registry-specific, data that
	* serves to represent the user.  For example,  for the UNIX user registry, the
	* UniqueId for a user can be the UID.
	* @exception EntryNotFoundException if userName does not exist.
	* @exception CustomRegistryException if there are any other problems.
	**/
	public String getUniqueUserId(String userName)
		throws CustomRegistryException, EntryNotFoundException
	{
		System.out.println("[DBRegistry] getUniqueUserId: " + userName);
		return userName;
	}
	/**
	* Returns the UniqueIds for all the users that belong to a group.
	* @param uniqueGroupId is the uniqueId of the group.
	* @return a List of all the user Unique ids that are contained in the
	* group whose Unique id matches the uniqueGroupId.
	* The Unique id for an entry is the stringified form of some unique,
	* registry-specific, data that serves to represent the entry.  For example, for the
	* Unix user registry, the Unique id for a group could be the GID and the
	* Unique Id for the user could be the UID.
	* @exception EntryNotFoundException if uniqueGroupId does not exist.
	* @exception CustomRegistryException if there are any other problems.
	**/
	public List getUniqueUserIds(String uniqueGroupId)
		throws CustomRegistryException, EntryNotFoundException
	{
		System.out.println("[DBRegistry] getUniqueUserIds: " + uniqueGroupId);
		List usrsForGroup = new ArrayList();
		Connection conn = null;
		Statement stmt = null;
		ResultSet rst = null;
		try
		{
			conn = getConnection();
			stmt = conn.createStatement();
			rst =
				stmt.executeQuery(
					"SELECT USER_ID FROM REGSCHEMA.USER_GROUP WHERE GROUP_ID='"
						+ uniqueGroupId
						+ "'");
			while (rst.next())
			{
				usrsForGroup.add(rst.getString("USER_ID"));
			}
		}
		catch (Exception ex)
		{
			if (!isValidGroup(uniqueGroupId))
			{
				throw new EntryNotFoundException(uniqueGroupId);
			}
			throw new CustomRegistryException(ex.getMessage());
		}
		finally
		{
			try
			{
				rst.close();
			}
			catch (SQLException sqle)
			{
			}
			try
			{
				stmt.close();
			}
			catch (SQLException sqle)
			{
			}
			try
			{
				conn.close();
			}
			catch (SQLException sqle)
			{
			}
		}
		return usrsForGroup;
	}
	/**
	* Returns the name for a user given its uniqueId.
	* @param uniqueUserId the UniqueId of the user.
	* @return the name of the user.
	* @exception EntryNotFoundException if the uniqueUserId does not exist.
	* @exception CustomRegistryException if there are any other problems.
	**/
	public String getUserSecurityName(String uniqueUserId)
		throws CustomRegistryException, EntryNotFoundException
	{
		System.out.println("[DBRegistry] getUserSecurityName: " + uniqueUserId);
		return uniqueUserId;
	}
	/**
	* Determines if a user exists.
	* @param userName is the name of the user.
	* @return true if the user exists; false otherwise.
	* @exception CustomRegistryException if there are any other problems.
	**/
	public boolean isValidUser(String userName) throws CustomRegistryException
	{
		System.out.println("[DBRegistry] isValidUser: " + userName);
		Connection conn = null;
		Statement stmt = null;
		ResultSet rst = null;
		boolean isValid = false;
		try
		{
			conn = getConnection();
			stmt = conn.createStatement();
			rst =
				stmt.executeQuery(
					"SELECT USER_ID FROM REGSCHEMA.USER WHERE USER_ID='"
						+ userName
						+ "'");
			if (rst.next())
			{
				isValid = true;
			}
		}
		catch (Exception ex)
		{
			throw new CustomRegistryException(ex.getMessage());
		}
		finally
		{
			try
			{
				rst.close();
			}
			catch (SQLException sqle)
			{
			}
			try
			{
				stmt.close();
			}
			catch (SQLException sqle)
			{
			}
			try
			{
				conn.close();
			}
			catch (SQLException sqle)
			{
			}
		}
		return isValid;
	}
	/**
	* Returns names of all the groups in the registry.
	* @return a List of the names of all the groups.
	* @exception CustomRegistryException if there are any other problems.
	**/
	public List getGroups() throws CustomRegistryException
	{
		System.out.println("[DBRegistry] getGroups");
		List allGroups = new ArrayList();
		Connection conn = null;
		Statement stmt = null;
		ResultSet rst = null;
		try
		{
			conn = getConnection();
			stmt = conn.createStatement();
			rst = stmt.executeQuery("SELECT GROUP_ID FROM REGSCHEMA.GROUP");
			while (rst.next())
			{
				allGroups.add(rst.getString("GROUP_ID"));
			}
		}
		catch (Exception ex)
		{
			throw new CustomRegistryException(ex.getMessage());
		}
		finally
		{
			try
			{
				rst.close();
			}
			catch (SQLException sqle)
			{
			}
			try
			{
				stmt.close();
			}
			catch (SQLException sqle)
			{
			}
			try
			{
				conn.close();
			}
			catch (SQLException sqle)
			{
			}
		}
		return allGroups;
	}
	/**
	* Returns names of the groups in the registry that match a pattern.
	* @param pattern is the pattern to match. (For example, a*  matches all
	* group names starting with a). At a minimum when a full name is used
	* as the pattern, the full name should be returned  if it is a
	* valid group.
	* @return a List of the names of the groups.
	* @exception CustomRegistryException if there are any other problems.
	**/
	public List getGroups(String pattern) throws CustomRegistryException
	{
		System.out.println("[DBRegistry] getGroups, pattern: " + pattern);
		List allGroups = new ArrayList();
		Connection conn = null;
		Statement stmt = null;
		ResultSet rst = null;
		try
		{
			conn = getConnection();
			stmt = conn.createStatement();
			rst = stmt.executeQuery("SELECT GROUP_ID FROM REGSCHEMA.GROUP");
			while (rst.next())
			{
				allGroups.add(rst.getString("GROUP_ID"));
			}
		}
		catch (Exception ex)
		{
			throw new CustomRegistryException(ex.getMessage());
		}
		finally
		{
			try
			{
				rst.close();
			}
			catch (SQLException sqle)
			{
			}
			try
			{
				stmt.close();
			}
			catch (SQLException sqle)
			{
			}
			try
			{
				conn.close();
			}
			catch (SQLException sqle)
			{
			}
		}
		return allGroups;
	}
	/**
	* Returns the names of the groups to which userName belongs.
	* @param userName is the username of the user.
	* @return a List of the names of all the groups to which the user belongs.
	* @exception EntryNotFoundException if userName does not exist.
	* @exception CustomRegistryException if there are any other problems.
	**/
	public List getGroupsForUser(String userName)
		throws CustomRegistryException, EntryNotFoundException
	{
		System.out.println("[DBRegistry] getGroupsForUser: " + userName);
		List usrsForGroup = new ArrayList();
		Connection conn = null;
		Statement stmt = null;
		ResultSet rst = null;
		try
		{
			conn = getConnection();
			stmt = conn.createStatement();
			rst =
				stmt.executeQuery(
					"SELECT GROUP_ID FROM REGSCHEMA.USER_GROUP WHERE USER_ID='"
						+ userName
						+ "'");
			while (rst.next())
			{
				usrsForGroup.add(rst.getString("GROUP_ID"));
			}
			if (usrsForGroup.size() == 0)
			{
				throw new Exception();
			}
		}
		catch (Exception ex)
		{
			if (!isValidGroup(userName))
			{
				throw new EntryNotFoundException(userName);
			}
			throw new CustomRegistryException(ex.getMessage());
		}
		finally
		{
			try
			{
				rst.close();
			}
			catch (SQLException sqle)
			{
			}
			try
			{
				stmt.close();
			}
			catch (SQLException sqle)
			{
			}
			try
			{
				conn.close();
			}
			catch (SQLException sqle)
			{
			}
		}
		return usrsForGroup;
	}
	/**
	* Returns the display name for a group.
	* @param groupName is the name of the group.
	* @return the display name for the group. The display name
	* is a registry-specific string that represents a descriptive, not
	* necessarily a unique, name for a group.
	* @exception EntryNotFoundException if the groupName does not exist.
	* @exception CustomRegistryException if there are any other problems.
	**/
	public String getGroupDisplayName(String groupName)
		throws CustomRegistryException, EntryNotFoundException
	{
		System.out.println("[DBRegistry] getGroupDisplayName: " + groupName);
		return groupName;
	}
	/**
	* Returns the Unique id for a group.
	* @param groupName is the name of the group.
	* @return the Unique id of the group. The Unique id for
	* a group is the stringified form of some unique, registry-specific,
	* data that serves to represent the entry.  For exmaple, for the
	* Unix user registry, the Unique id could be the GID for the entry.
	* @exception EntryNotFoundException if groupName does not exist.
	* @exception CustomRegistryException if there are any other problems.
	**/
	public String getUniqueGroupId(String groupName)
		throws CustomRegistryException, EntryNotFoundException
	{
		System.out.println("[DBRegistry] getUniqueGroupId: " + groupName);
		return groupName;
	}
	/**
	* Returns the Unique id for a group.
	* @param groupName is the name of the group.
	* @return the Unique id of the group. The Unique id for
	* a group is the stringified form of some unique, registry-specific,
	* data that serves to represent the entry. For example, for the
	* Unix user registry, the Unique id could be the GID for the entry.
	* @exception EntryNotFoundException if groupName does not exist.
	* @exception CustomRegistryException if there are any other problems.
	**/
	public List getUniqueGroupIds(String uniqueUserId)
		throws CustomRegistryException, EntryNotFoundException
	{
		System.out.println("[DBRegistry] getUniqueGroupIds: " + uniqueUserId);
		List usrsForGroup = new ArrayList();
		Connection conn = null;
		Statement stmt = null;
		ResultSet rst = null;
		try
		{
			conn = getConnection();
			stmt = conn.createStatement();
			rst =
				stmt.executeQuery(
					"SELECT GROUP_ID FROM REGSCHEMA.USER_GROUP WHERE USER_ID='"
						+ uniqueUserId
						+ "'");
			while (rst.next())
			{
				usrsForGroup.add(rst.getString("GROUP_ID"));
			}
			if (usrsForGroup.size() == 0)
			{
				throw new Exception();
			}
		}
		catch (Exception ex)
		{
			if (!isValidGroup(uniqueUserId))
			{
				throw new EntryNotFoundException(uniqueUserId);
			}
			throw new CustomRegistryException(ex.getMessage());
		}
		finally
		{
			try
			{
				rst.close();
			}
			catch (SQLException sqle)
			{
			}
			try
			{
				stmt.close();
			}
			catch (SQLException sqle)
			{
			}
			try
			{
				conn.close();
			}
			catch (SQLException sqle)
			{
			}
		}
		return usrsForGroup;
	}
	/**
	* Returns the name for a group given its uniqueId.
	* @param uniqueGroupId is the UniqueId of the group.
	* @return the name of the group.
	* @exception EntryNotFoundException if the uniqueGroupId does not exist.
	* @exception CustomRegistryException if there are any other problems.
	**/
	public String getGroupSecurityName(String uniqueGroupId)
		throws CustomRegistryException, EntryNotFoundException
	{
		System.out.println(
			"[DBRegistry] getGroupSecurityName: " + uniqueGroupId);
		return uniqueGroupId;
	}
	/**
	* Determines if a group exists.
	* @param groupName is the name of the group.
	* @return true if the group exists; false otherwise.
	* @exception CustomRegistryException if there are any other problems.
	**/
	public boolean isValidGroup(String groupName)
		throws CustomRegistryException
	{
		System.out.println("[DBRegistry] isValidGroup: " + groupName);
		Connection conn = null;
		Statement stmt = null;
		ResultSet rst = null;
		boolean isValid = false;
		try
		{
			conn = getConnection();
			stmt = conn.createStatement();
			rst =
				stmt.executeQuery(
					"SELECT GROUP_ID FROM REGSCHEMA.GROUP WHERE GROUP_ID='"
						+ groupName
						+ "'");
			if (rst.next())
			{
				isValid = true;
			}
		}
		catch (Exception ex)
		{
			throw new CustomRegistryException(ex.getMessage());
		}
		finally
		{
			try
			{
				rst.close();
			}
			catch (SQLException sqle)
			{
			}
			try
			{
				stmt.close();
			}
			catch (SQLException sqle)
			{
			}
			try
			{
				conn.close();
			}
			catch (SQLException sqle)
			{
			}
		}
		return isValid;
	}
}